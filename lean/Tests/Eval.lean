import Les

/-
段階 A・B を含む現在の Lean 評価器と、固定 Go CLI で観測したコーパス期待値を比較する。
使い方: lake exe les-eval-test ../lesdump/golden ../difftest/corpus [fuel]
35 件を PASS / FAIL / OUT_OF_FUEL / UNSUPPORTED に分類し、UNSUPPORTED は PASS に数えない。
`stageA` の 19 件は履歴上の内訳表示であり、判定は35件すべて PASS が必要。
-/
open Lean (Json)
open Les.Syntax Les.Eval

/-- 段階 A（P1c-4）の 19 件。内訳表示のためだけに使う。判定は全件 PASS 必須。 -/
def stageA : List String := [
  "basic-print", "print-no-newline", "exit-status", "div-zero-control",
  "lazy-unused-binding", "force-postfix-unused-binding", "force-basic",
  "rebind-forces-rhs", "rebind-old-binding", "rebind-discards-thunk",
  "snapshot-late-rebind", "forward-ref", "forward-ref-rebound", "blackhole",
  "exit-lazy", "error-keeps-output", "error-pos-bare-stmt",
  "alias-binding-not-forced", "ident-stmt-forces"]

structure Expect where
  stdout : String
  stderr : String
  exitCode : Int

def parseExpect (text : String) : Except String Expect := do
  let j ← Json.parse text
  let stdout ← j.getObjValAs? String "stdout"
  let exitCode ← j.getObjValAs? Int "exit_code"
  let stderr ← j.getObjValAs? String "stderr"
  return { stdout, stderr, exitCode }

inductive Res where
  | pass | fail (why : String) | outOfFuel | unsupported (why : String)

def judge (e : Expect) : Verdict → Res
  | .observed o =>
    let bad := (if o.stdout != e.stdout then ["stdout"] else []) ++
      (if o.exitCode != e.exitCode then ["exit_code"] else []) ++
      (if e.stderr != o.stderr then ["stderr"] else [])
    if bad.isEmpty then .pass
    else .fail s!"{bad} lean={repr o} expected stdout={repr e.stdout} stderr={repr e.stderr} exit={e.exitCode}"
  | .unsupported w => .unsupported w
  | .outOfFuel => .outOfFuel
  | .internal m => .fail m

def Res.tag : Res → String
  | .pass => "PASS" | .fail _ => "FAIL" | .outOfFuel => "OUT_OF_FUEL" | .unsupported _ => "UNSUPPORTED"

def progOf (src : String) : Except String CheckedProgram := do
  (← decodeProgramString src).check

def verdictOf (fuel : Nat) (src : String) : Except String Verdict := do
  return (run fuel (← progOf src)).verdict

structure T where
  fails : IO.Ref Nat

def T.check (t : T) (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then IO.println s!"PASS  {name}"
  else
    t.fails.modify (· + 1)
    IO.println s!"FAIL  {name} {detail}"


/-! ## 個別テスト（AST を直接組む。位置は 1 行目の連番で、結果の比較には使わない） -/

def P (c : Nat := 1) (l : Nat := 1) : Pos := { line := l, col := c }
def ident (n : String) : Expr := .ident (P) n
def sInt (i : Int) : Expr := .int (P) i
def sStr (s : String) : Expr := .str (P) s
def add (a b : Expr) : Expr := .binary (P) "+" a b
def printE (args : List Expr) : Expr := .call (P) (ident "print") args
def assign (n : String) (e : Expr) : Stmt := .varDecl (P) n "" e
def stmtE (e : Expr) : Stmt := .expr (P) e

def mkProg (body : List Stmt) : CheckedProgram :=
  { program := { analysis := { status := .ok, typeError := "", typeWarnings := [] }, body },
    ok := rfl }

def globalCell (m : Machine) (n : String) : Option Cell :=
  (m.heap.lookupLocal globalScope n).bind m.heap.cell?

def isDoneInt (c : Option Cell) (i : Int) : Bool :=
  match c with | some (.done (.int j)) => i == j | _ => false

def callE (f : String) (args : List Expr := []) : Expr := .call (P) (ident f) args
def prm (n : String) : Param := { pos := P, name := n, typeAnnot := "" }
def defn (n : String) (ps : List String) (body : List Stmt) : Stmt := .funcDef (P) n (ps.map prm) "" body
/-- 副作用つきの 0 引数関数: `def g(): print "side;"; 1` -/
def gDef : Stmt := defn "g" [] [stmtE (printE [sStr "side;"]), stmtE (sInt 1)]

def unitTests (t : T) : IO Unit := do
  IO.println "== unit tests =="
  -- 期待値の stderr 欠落は FAIL（stderr は必須。暗黙に照合を省かない）。
  t.check "expect.json without stderr is rejected"
    (match parseExpect "{\"stdout\": \"\", \"exit_code\": 0}" with | .error _ => true | .ok _ => false)
  t.check "expect.json with stderr is accepted"
    (match parseExpect "{\"stdout\": \"\", \"stderr\": \"\", \"exit_code\": 0}" with | .ok _ => true | .error _ => false)
  -- (1) Heap 共有・メモ化: 副作用つき Thunk は何度要求しても 1 回だけ実行される（E9）。
  let (o, m) := runMachine 100 (mkProg [
    assign "x" (printE [sStr "s;"]), stmtE (ident "x"), stmtE (ident "x"), stmtE (ident "x")])
  t.check "memo: side effect of a shared thunk happens once" (o.stdout == "s;" && o.halt.isNone) s!"{repr o}"
  t.check "memo: forced thunk is overwritten with done"
    (match globalCell m "x" with | some (.done .unit) => true | _ => false)
  -- (2) 同じ Cell を 2 つの引数で共有し、強制後は done の値になる（E10, E11 の識別子引数）。
  let (o, m) := runMachine 100 (mkProg [
    assign "a" (add (sInt 1) (sInt 2)), stmtE (printE [ident "a", ident "a"])])
  t.check "sharing: two uses of one binding print the memoized value" (o.stdout == "33") s!"{repr o}"
  t.check "sharing: binding holds done 3 afterwards" (isDoneInt (globalCell m "a") 3)
  -- (3) 遅延: 強制されない束縛は suspended のまま（E1）。
  let (_, m) := runMachine 100 (mkProg [assign "x" (add (sInt 1) (sInt 2))])
  t.check "lazy: unforced binding stays suspended"
    (match globalCell m "x" with | some (.suspended ..) => true | _ => false)
  -- (4) ブラックホール検出（E16）: 位置なし、それまでの出力は残り、Cell は blackhole のまま。
  let (o, m) := runMachine 100 (mkProg [
    assign "x" (add (ident "x") (sInt 1)), stmtE (printE [sStr "ok"]), stmtE (printE [ident "x"])])
  t.check "blackhole: positionless error, stdout kept"
    (match o.halt with
     | some (.error msg .absent) => o.stdout == "ok" && msg == "blackhole: circular reference detected in lazy thunk"
     | _ => false) s!"{repr o}"
  t.check "blackhole: the cell stays blackhole"
    (match globalCell m "x" with | some (.blackhole _) => true | _ => false)
  -- (5) 再束縛で古い Cell は破棄されず、先に作った Thunk のスナップショットから参照され続ける（E14）。
  let (_, m) := runMachine 100 (mkProg [
    assign "a" (sInt 1), assign "b" (add (ident "a") (sInt 1)), assign "a" (sInt 10)])
  let oldAddr? : Option Addr :=
    match globalCell m "b" with
    | some (.suspended _ env) => (env.snap.find? (·.1 == "a")).map (·.2)
    | _ => none
  let newAddr? := m.heap.lookupLocal globalScope "a"
  t.check "rebind: b's snapshot points at the old cell, not the new binding"
    (oldAddr?.isSome && newAddr?.isSome && oldAddr? != newAddr?)
  t.check "rebind: old cell is still done 1" (isDoneInt (oldAddr?.bind m.heap.cell?) 1)
  t.check "rebind: new binding holds done 10" (isDoneInt (globalCell m "a") 10)
  -- (6) 再束縛は右辺を即時評価する（E3）: 未使用でもエラー。
  let o := run 100 (mkProg [assign "x" (sInt 1), assign "x" (.binary (P 7 2) "/" (sInt 1) (sInt 0))])
  t.check "rebind: rhs is forced immediately"
    (match o.halt with | some (.error "division by zero" (.at p)) => p.col == 7 && p.line == 2 | _ => false)
  -- (7) fuel: 足りなければ OUT_OF_FUEL で、PASS にも FAIL にも数えない。
  let o := run 0 (mkProg [stmtE (printE [sStr "a"])])
  t.check "fuel: 0 fuel is outOfFuel" (match o.halt with | some .outOfFuel => true | _ => false)
  t.check "fuel: outOfFuel verdict is not an observation"
    (match o.verdict with | .outOfFuel => true | _ => false)
  let o := run 3 (mkProg [stmtE (printE [add (add (sInt 1) (sInt 2)) (add (sInt 3) (sInt 4))])])
  t.check "fuel: small fuel on a deep expression is outOfFuel"
    (match o.halt with | some .outOfFuel => true | _ => false) s!"{repr o}"
  let o := run 100 (mkProg [stmtE (printE [add (add (sInt 1) (sInt 2)) (add (sInt 3) (sInt 4))])])
  t.check "fuel: enough fuel decides" (o.stdout == "10" && o.halt.isNone)
  -- (8) 未対応は UNSUPPORTED で、PASS ではない。
  let o := run 100 (mkProg [stmtE (printE [sStr "a"]), stmtE (ident "print"), stmtE (printE [sStr "b"])])
  t.check "unsupported: 0-argument builtin call halts, later statements do not run"
    (match o.verdict with | .unsupported _ => o.stdout == "a" | _ => false) s!"{repr o}"
  let o := run 100 (mkProg [stmtE (printE [.binary (P) "+" (sStr "a") (sStr "b")])])
  t.check "unsupported: String + String is unsupported"
    (match o.verdict with | .unsupported _ => true | _ => false)
  -- (9) 位置: 内側の強制式の位置が優先され、文頭は裸の文だけ（E21）。
  let o := run 100 (mkProg [stmtE (printE [add (sInt 5) (.binary (P 14) "/" (sInt 1) (sInt 0))])])
  t.check "position: innermost forced expression wins (col 14)"
    (match o.halt with | some (.error _ (.at p)) => p.col == 14 | _ => false)
  -- (10) 左から右の強制順（E17）: 両方が失敗するとき、報告されるのは左のエラー。
  let bad (c : Nat) : Expr := .binary (P c) "/" (sInt 1) (sInt 0)
  let o := run 100 (mkProg [stmtE (printE [sInt 0, add (bad 3) (bad 9)])])
  t.check "order: binary operands are forced left to right (col 3)"
    (match o.halt with | some (.error _ (.at p)) => p.col == 3 | _ => false) s!"{repr o}"
  let o := run 100 (mkProg [stmtE (printE [bad 5, bad 11])])
  t.check "order: print arguments are forced left to right (col 5)"
    (match o.halt with | some (.error _ (.at p)) => p.col == 5 | _ => false) s!"{repr o}"
  -- ===== 段階 B（def・呼び出し・closure）=====
  -- (11) 引数の共有・メモ化（E9, E10）: `twice(a) = a + a` に `twice(g())` → 副作用は 1 回。
  let o := run 200 (mkProg [gDef, defn "twice" ["a"] [stmtE (add (ident "a") (ident "a"))],
    stmtE (printE [callE "twice" [callE "g"]])])
  t.check "args: compound argument is one shared thunk (side;2)" (o.stdout == "side;2" && o.halt.isNone) s!"{repr o}"
  -- (12) 識別子引数は既存の Cell を共有し、呼び出し時には強制しない（E11）。
  let o := run 200 (mkProg [assign "n" (.binary (P 7 1) "/" (sInt 1) (sInt 0)),
    defn "f" ["a"] [stmtE (sInt 1)], stmtE (printE [callE "f" [ident "n"]])])
  t.check "args: unused identifier argument is never forced" (o.stdout == "1" && o.halt.isNone) s!"{repr o}"
  let (o, m) := runMachine 200 (mkProg [assign "n" (callE "g"), gDef,
    defn "h" ["a"] [stmtE (add (ident "a") (sInt 0))], stmtE (printE [callE "h" [ident "n"], ident "n"])])
  t.check "args: callee forcing the parameter also forces the caller's binding (side;11)"
    (o.stdout == "side;11") s!"{repr o}"
  t.check "args: the caller's binding holds done 1 afterwards" (isDoneInt (globalCell m "n") 1)
  -- (13) 呼び出しごとの子スコープ・局所束縛（E12）: `x = 1; def f(): x = 2; x` → `2;1`。
  let (o, m) := runMachine 200 (mkProg [assign "x" (sInt 1), defn "f" [] [assign "x" (sInt 2), stmtE (ident "x")],
    stmtE (printE [callE "f", sStr ";", ident "x"])])
  t.check "scope: binding inside a function is local (2;1)" (o.stdout == "2;1") s!"{repr o}"
  t.check "scope: global x untouched" (isDoneInt (globalCell m "x") 1)
  -- (14) closure は定義時の生きたスコープを保持する（E13）: `3;4`（スナップショットなら `3;3`）。
  let o := run 200 (mkProg [assign "y" (sInt 3), defn "f" [] [stmtE (ident "y")],
    stmtE (printE [callE "f", sStr ";"]), assign "y" (sInt 4), stmtE (printE [callE "f"])])
  t.check "closure: body sees the later rebinding of a global (3;4)" (o.stdout == "3;4") s!"{repr o}"
  -- 呼び出し元ではなく定義時のスコープが親になる（字句スコープ。Go CLI: `3`）。
  let o := run 200 (mkProg [assign "y" (sInt 3), defn "f" [] [stmtE (ident "y")],
    defn "g" [] [assign "y" (sInt 99), stmtE (callE "f")], stmtE (printE [callE "g"])])
  t.check "closure: parent scope is the definition scope, not the caller's (3)" (o.stdout == "3") s!"{repr o}"
  -- 関数内の def は、その呼び出しの子スコープを保持する。
  let o := run 200 (mkProg [defn "mk" [] [assign "k" (sInt 5), defn "inner" [] [stmtE (ident "k")], stmtE (callE "inner")],
    stmtE (printE [callE "mk"])])
  t.check "closure: a def inside a call keeps that call's scope (5)" (o.stdout == "5") s!"{repr o}"
  -- (15) E22: 識別子だけの文は 0 引数で呼び出す。値の文の値は最後の式文。
  let o := run 200 (mkProg [defn "hello" [] [stmtE (printE [sStr "hi;"]), stmtE (sInt 1)],
    stmtE (ident "hello"), stmtE (printE [sStr "end"])])
  t.check "E22: bare identifier statement calls a 0-argument def (hi;end)" (o.stdout == "hi;end" && o.halt.isNone) s!"{repr o}"
  let o := run 200 (mkProg [defn "body" [] [stmtE (printE [sStr "a;"]), stmtE (sInt 2), stmtE (printE [sStr "b;"]), stmtE (sInt 3)],
    stmtE (printE [callE "body"])])
  t.check "call: value is the last expression statement (a;b;3)" (o.stdout == "a;b;3") s!"{repr o}"
  -- (16) newCapturedThunk: 既に snap を持つ環境の中で作る引数 Thunk は、その snap から捕捉する。
  -- `a = 1; def f(p): p; b = f(a + 1); a = 10; print b` → `2`（Go CLI で確認。live スコープだけを見ると 11）。
  let o := run 200 (mkProg [assign "a" (sInt 1), defn "f" ["p"] [stmtE (ident "p")],
    assign "b" (callE "f" [add (ident "a") (sInt 1)]), assign "a" (sInt 10), stmtE (printE [ident "b"])])
  t.check "capture: argument thunk built inside a snapshot env uses the snapshot (2)" (o.stdout == "2") s!"{repr o}"
  -- 引数の識別子が作成時に未束縛なら強制時に生きたスコープから引く（E15。Go CLI: `5` / `7`）。
  let o := run 200 (mkProg [defn "f" ["p"] [stmtE (ident "p")], assign "b" (callE "f" [ident "z"]),
    assign "z" (sInt 5), stmtE (printE [ident "b"])])
  t.check "capture: unbound identifier argument resolves at force time (5)" (o.stdout == "5") s!"{repr o}"
  let o := run 200 (mkProg [defn "f" ["p"] [stmtE (ident "p")], assign "b" (callE "f" [add (ident "z") (sInt 0)]),
    assign "z" (sInt 5), assign "z" (sInt 7), stmtE (printE [ident "b"])])
  t.check "capture: unbound name inside a compound argument sees the latest binding (7)" (o.stdout == "7") s!"{repr o}"
  -- 作成時に未束縛で、最後まで束縛されない識別子引数は呼び出し時に評価しない（Go CLI: `1`）。
  -- 準備時に即時に引くと「undefined identifier」で止まる。
  let o := run 200 (mkProg [defn "f" ["p"] [stmtE (sInt 1)], stmtE (printE [callE "f" [ident "z"]])])
  t.check "capture: never-bound identifier argument is deferred, not looked up at call time (1)"
    (o.stdout == "1" && o.halt.isNone) s!"{repr o}"
  -- 引数が複数足りない呼び出し: 欠けた仮引数は `done unit` に束縛され、本体で読める。
  -- 注: Go の型検査は引数不足を静的に拒否する（`function expects at least 2 arguments`）ので、
  -- CheckedProgram では起きない。評価器が全域であることの防御的な AST テスト。
  let (o, m) := runMachine 200 (mkProg [defn "f" ["a", "b"] [stmtE (ident "a"), stmtE (ident "b"), stmtE (printE [sStr "ok"])],
    stmtE (callE "f")])
  t.check "call: several omitted parameters are readable in the body (no halt)"
    (o.stdout == "ok" && o.halt.isNone) s!"{repr o}"
  t.check "call: omitted parameters are bound to done unit"
    (m.heap.cells.any (fun c => match c with | .done .unit => true | _ => false))
  -- (17) 引数不足は unit、余りは無視。
  let o := run 200 (mkProg [defn "f" ["p"] [stmtE (sInt 1)], stmtE (printE [callE "f" [sInt 9, sInt 9]])])
  t.check "call: extra arguments are ignored" (o.stdout == "1")
  -- (18) 再帰と fuel: 自己呼び出しは fuel で止まり OUT_OF_FUEL（PASS にならない）。
  let o := run 50 (mkProg [defn "loop" [] [stmtE (callE "loop")], stmtE (callE "loop")])
  t.check "fuel: infinite recursion ends as outOfFuel" (match o.verdict with | .outOfFuel => true | _ => false) s!"{repr o}"

def main (args : List String) : IO UInt32 := do
  let t : T := { fails := ← IO.mkRef 0 }
  let goldenDir : System.FilePath := args.headD "../lesdump/golden"
  let corpusDir : System.FilePath := (args.drop 1).headD "../difftest/corpus"
  let fuel := ((args.drop 2).head?.bind String.toNat?).getD 1000
  let entries ← corpusDir.readDir
  let names := (entries.filterMap fun e =>
      let n := e.fileName
      if n.endsWith ".expect.json" then some (n.dropRight ".expect.json".length) else none)
    |>.qsort (· < ·)
  let mut counts : Array (String × Nat) := #[("PASS", 0), ("FAIL", 0), ("OUT_OF_FUEL", 0), ("UNSUPPORTED", 0)]
  IO.println s!"== corpus vs Lean (fuel {fuel}) =="
  for n in names do
    let exp ← IO.FS.readFile (corpusDir / s!"{n}.expect.json")
    let src ← IO.FS.readFile (goldenDir / s!"{n}.json")
    let res : Res :=
      match parseExpect exp, verdictOf fuel src with
      | .error e, _ => .fail s!"bad expect.json: {e}"
      | _, .error e => .fail s!"decode/check: {e}"
      | .ok e, .ok v => judge e v
    let inA := stageA.contains n
    let note := match res with
      | .fail w => " " ++ w | .unsupported w => " (" ++ w ++ ")" | _ => ""
    IO.println s!"{res.tag}  {if inA then "[A]" else "[B]"} {n}{note}"
    counts := counts.map fun (k, c) => if k == res.tag then (k, c + 1) else (k, c)
    -- 全件 PASS 必須。FAIL / OUT_OF_FUEL / UNSUPPORTED が 1 件でもあれば全体が失敗。
    match res with
    | .pass => pure ()
    | _ => t.fails.modify (· + 1)
  unitTests t
  IO.println s!"summary: {counts.toList}"
  let missing := stageA.filter (!names.contains ·)
  t.check "all stage A cases exist in corpus" missing.isEmpty s!"{missing}"
  t.check "stage A has 19 cases" (stageA.length == 19)
  t.check "corpus has 35 cases" (names.size == 35) s!"{names.size}"
  t.check "every corpus case is PASS (no UNSUPPORTED / OUT_OF_FUEL)"
    (counts.toList == [("PASS", names.size), ("FAIL", 0), ("OUT_OF_FUEL", 0), ("UNSUPPORTED", 0)]) s!"{counts.toList}"
  let f ← t.fails.get
  IO.println (if f == 0 then "OK" else s!"{f} failure(s)")
  return (if f == 0 then 0 else 1)
