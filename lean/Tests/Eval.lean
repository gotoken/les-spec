import Les

/-
評価器（段階 A）と Go CLI の期待値の比較。
使い方: lake exe les-eval-test ../lesdump/golden ../difftest/corpus [fuel]
各ケースを PASS / FAIL / OUT_OF_FUEL / UNSUPPORTED に分ける。UNSUPPORTED は PASS に数えない。
-/
open Lean (Json)
open Les.Syntax Les.Eval

/-- 段階 A の対象（設計メモ 6 節 + P1c-3 のうちクロージャを使わない 19 件）。 -/
def stageA : List String := [
  "basic-print", "print-no-newline", "exit-status", "div-zero-control",
  "lazy-unused-binding", "force-postfix-unused-binding", "force-basic",
  "rebind-forces-rhs", "rebind-old-binding", "rebind-discards-thunk",
  "snapshot-late-rebind", "forward-ref", "forward-ref-rebound", "blackhole",
  "exit-lazy", "error-keeps-output", "error-pos-bare-stmt",
  "alias-binding-not-forced", "ident-stmt-forces"]

structure Expect where
  stdout : String
  stderr : Option String
  exitCode : Int

def parseExpect (text : String) : Except String Expect := do
  let j ← Json.parse text
  let stdout ← j.getObjValAs? String "stdout"
  let exitCode ← j.getObjValAs? Int "exit_code"
  let stderr := (j.getObjValAs? String "stderr").toOption
  return { stdout, stderr, exitCode }

inductive Res where
  | pass | fail (why : String) | outOfFuel | unsupported (why : String)

def judge (e : Expect) : Verdict → Res
  | .observed o =>
    let bad := (if o.stdout != e.stdout then ["stdout"] else []) ++
      (if o.exitCode != e.exitCode then ["exit_code"] else []) ++
      (match e.stderr with | some s => if s != o.stderr then ["stderr"] else [] | none => [])
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

def unitTests (t : T) : IO Unit := do
  IO.println "== unit tests =="
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
  let o := run 100 (mkProg [.funcDef (P) "f" [] "" [], stmtE (printE [sStr "x"])])
  t.check "unsupported: def halts as unsupported, later statements do not run"
    (match o.verdict with | .unsupported _ => o.stdout == "" | _ => false)
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
    -- 段階 A の 19 件は PASS 必須。それ以外は FAIL でなければよい（UNSUPPORTED が正常）。
    match res with
    | .pass => pure ()
    | .unsupported _ => if inA then t.fails.modify (· + 1)
    | _ => t.fails.modify (· + 1)
  unitTests t
  IO.println s!"summary: {counts.toList}"
  let missing := stageA.filter (!names.contains ·)
  t.check "all stage A cases exist in corpus" missing.isEmpty s!"{missing}"
  t.check "stage A has 19 cases" (stageA.length == 19)
  let f ← t.fails.get
  IO.println (if f == 0 then "OK" else s!"{f} failure(s)")
  return (if f == 0 then 0 else 1)
