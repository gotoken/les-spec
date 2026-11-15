import Les.Eval.Heap

/-
段階 A の評価器（docs/evaluator-design.md 4 節）。fuel を構造再帰の引数にした全域関数で、
`partial` / `sorry` / `unsafe` は使わない。fuel は呼び出しの入れ子の深さの上限。
段階 A で扱わないもの: `def`・ユーザー関数の呼び出し・0 引数の組込み呼び出し・
Int 以外／負数の算術。これらは `Halt.unsupported`（比較では UNSUPPORTED）。
-/
namespace Les.Eval
open Les.Syntax

def Halt.attach (p : Pos) : Halt → Halt
  | .error m .pending => .error m (.at p)
  | h => h

private def getHeap : EvalM Heap := do return (← get).heap
private def modHeap (f : Heap → Heap) : EvalM Unit := modify fun m => { m with heap := f m.heap }

def alloc (c : Cell) : EvalM Addr :=
  modifyGet fun m =>
    let (h, a) := m.heap.alloc c
    (a, { m with heap := h })

/-- 原始エラー。位置は最も内側の demand / whnf / exec が付ける（E21）。 -/
def primErr (msg : String) : EvalM α := throw (.error msg .pending)

def lookupEnv (heap : Heap) (env : Env) (n : String) : Option Addr :=
  match env.snap.find? (·.1 == n) with
  | some (_, a) => some a
  | none => heap.lookup env.scope n

/-- 作成時点で見えている名前だけをスナップショットする（E14, E15）。 -/
def capture (e : Expr) (scope : ScopeId) : EvalM Env := do
  let heap ← getHeap
  let names := (exprNames e).eraseDups
  let snap := names.filterMap fun n => (heap.lookup scope n).map (n, ·)
  return { snap, scope }

def arith (op : String) (a b : Value) : EvalM Value :=
  match a, b with
  | .int x, .int y =>
    match op with
    | "+" => pure (.int (x + y))
    | "-" => pure (.int (x - y))
    | "*" => pure (.int (x * y))
    | "/" =>
      if y == 0 then primErr "division by zero"
      else if x < 0 || y < 0 then throw (.unsupported "Int division with a negative operand")
      else pure (.int (x / y))
    | _ => throw (.unsupported s!"operator {op}")
  | _, _ => throw (.unsupported s!"operator {op} on non-Int operands")

def showValue : Value → EvalM String
  | .int i => pure (toString i)
  | .str s => pure s
  | _ => throw (.unsupported "print of a non-Int/String value")

mutual
/-- 式を評価して Cell を返す。変数参照は強制しない（E2）。 -/
def evalE : Nat → Expr → Env → EvalM Addr
  | 0, _, _ => throw .outOfFuel
  | n + 1, e, env =>
    match e with
    | .int _ i => alloc (.done (.int i))
    | .str _ s => alloc (.done (.str s))
    | .ident _ name => do
      match lookupEnv (← getHeap) env name with
      | some a => pure a
      | none => primErr s!"undefined identifier: {name}"
    | .binary _ op l r => do
      let a ← demand n l env
      let b ← demand n r env
      let v ← arith op a b
      alloc (.done v)
    | .force _ x => do
      let v ← demand n x env
      alloc (.done v)
    | .call _ callee args => do
      let f ← demand n callee env
      match f with
      | .builtin b => callBuiltin n b args env
      | _ => throw (.unsupported "call of a user function (stage B)")

/-- Cell を強制して値にする。共有・メモ化・ブラックホール（E9, E16）。 -/
def whnf : Nat → Addr → EvalM Value
  | 0, _ => throw .outOfFuel
  | n + 1, a => do
    match (← getHeap).cell? a with
    | none => throw (.error "internal: dangling address" .absent)
    | some (.done v) => pure v
    | some (.blackhole _) =>
      throw (.error "blackhole: circular reference detected in lazy thunk" .absent)
    | some (.suspended e env) => do
      modHeap (·.setCell a (.blackhole e))
      let v ← demand n e env
      modHeap (·.setCell a (.done v))
      pure v

/-- `evalE` してから `whnf`。`pending` のエラーに式の位置を付ける（E21）。 -/
def demand : Nat → Expr → Env → EvalM Value
  | 0, _, _ => throw .outOfFuel
  | n + 1, e, env =>
    tryCatch (do let a ← evalE n e env; whnf n a) fun h => throw (h.attach (exprPos e))

/-- 組込みの呼び出し。引数は先に左から準備し（force は準備時に評価: E6, E11）、
    その後 `print` は左から強制（E19）、`exit` は強制して終了（E20）。 -/
def callBuiltin : Nat → Builtin → List Expr → Env → EvalM Addr
  | 0, _, _, _ => throw .outOfFuel
  | n + 1, b, args, env => do
    let cells ← prepArgs n args env
    match b with
    | .print => do
      let vals ← forceAll n cells
      let parts ← vals.mapM showValue
      modify fun m => { m with stdout := m.stdout ++ String.join parts }
      alloc (.done .unit)
    | .exit =>
      match cells with
      | [] => throw (.exit 0)
      | [c] => do
        match ← whnf n c with
        | .int i => throw (.exit i)
        | _ => throw (.unsupported "exit with a non-Int argument")
      | _ => throw (.unsupported "exit with several arguments")

def prepArgs : Nat → List Expr → Env → EvalM (List Addr)
  | 0, _, _ => throw .outOfFuel
  | _ + 1, [], _ => pure []
  | n + 1, a :: as, env => do
    let c ← prepArg n a env
    let cs ← prepArgs n as env
    pure (c :: cs)

def prepArg : Nat → Expr → Env → EvalM Addr
  | 0, _, _ => throw .outOfFuel
  | n + 1, a, env =>
    match a with
    | .int .. | .str .. | .force .. => evalE n a env   -- リテラルは done、force は評価済み（E11）
    | .ident .. => evalE n a env                       -- 既存の Cell をそのまま（E11）
    | _ => alloc (.suspended a env)                    -- それ以外は未評価 Thunk

def forceAll : Nat → List Addr → EvalM (List Value)
  | 0, _ => throw .outOfFuel
  | _ + 1, [] => pure []
  | n + 1, c :: cs => do
    let v ← whnf n c
    let vs ← forceAll n cs
    pure (v :: vs)
end

/-- 文の実行。値を返すのは式文だけ。`pending` のエラーに文の位置を付ける。 -/
def exec : Nat → Stmt → ScopeId → EvalM (Option Addr)
  | 0, _, _ => throw .outOfFuel
  | n + 1, s, sc =>
    tryCatch (execCore n s sc) fun h => throw (h.attach (stmtPos s))
where
  execCore (n : Nat) (s : Stmt) (sc : ScopeId) : EvalM (Option Addr) :=
    match s with
    | .funcDef .. => throw (.unsupported "def (stage B)")
    | .expr _ (.ident p name) => do
      let env : Env := { snap := [], scope := sc }
      let c ← evalE n (.ident p name) env
      match ← whnf n c with
      | .closure .. => throw (.unsupported "0-argument call of a user function (stage B)")
      | .builtin _ => throw (.unsupported "0-argument call of a builtin")
      | _ => pure (some c)
    | .expr _ e => do
      let c ← evalE n e { snap := [], scope := sc }
      pure (some c)
    | .varDecl _ name _ rhs => do
      let env : Env := { snap := [], scope := sc }
      let heap ← getHeap
      let cell ←
        if (heap.lookupLocal sc name).isSome then
          -- 再束縛: 右辺をその場で強制し、評価済みで置き換える（E3, E4, E5）
          let v ← demand n rhs env
          alloc (.done v)
        else
          match rhs with
          | .int .. | .str .. | .force .. => evalE n rhs env   -- 評価済み（E6）
          | _ => do alloc (.suspended rhs (← capture rhs sc))
      modHeap (·.bind sc name cell)
      pure none

def execAll (fuel : Nat) (ss : List Stmt) (sc : ScopeId) : EvalM Unit :=
  ss.forM fun s => do let _ ← exec fuel s sc; pure ()

/-- 実行して最終状態も返す（テスト用: Heap を検査できる）。 -/
def runMachine (fuel : Nat) (cp : CheckedProgram) : Outcome × Machine :=
  let m0 : Machine := { heap := Heap.initial, stdout := "" }
  let (r, m) := (execAll fuel cp.program.body globalScope).run.run m0
  ({ stdout := m.stdout, halt := match r with | .ok _ => none | .error h => some h }, m)

def run (fuel : Nat) (cp : CheckedProgram) : Outcome := (runMachine fuel cp).1

end Les.Eval
