import Les.Syntax

/-
`lesdump` の golden JSON を Lean で読み込むテスト。
使い方: lake exe les-syntax-test ../lesdump/golden [期待ファイル数]
-/
open Lean (Json)
open Les.Syntax

structure T where
  fails : IO.Ref Nat

def T.check (t : T) (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then
    IO.println s!"PASS {name}"
  else
    t.fails.modify (· + 1)
    IO.println s!"FAIL {name} {detail}"

/-- 入力を拒否し、エラー文に `needle` が含まれること。 -/
def T.rejects (t : T) (name : String) (input : String) (needle : String) : IO Unit :=
  match decodeProgramString input with
  | .ok _ => t.check name false "(accepted, expected an error)"
  | .error e => t.check name (needle.isPrefixOf e || (e.splitOn needle).length > 1) s!"(error was: {e})"

def okProgram (body : String) (status : String := "ok") : String :=
  "{\"schema_version\":1,\"kind\":\"Program\",\"analysis\":{\"status\":\"" ++ status ++
  "\",\"type_error\":\"\",\"type_warnings\":[]},\"body\":" ++ body ++ "}"

def p11 : String := "\"pos\":{\"line\":1,\"col\":1}"

def goldenTests (t : T) (dir : System.FilePath) (expected : Option Nat) : IO (List (String × Program)) := do
  let entries ← dir.readDir
  let files := (entries.map (·.path)).filter (·.extension == some "json")
  let files := files.qsort (fun a b => a.toString < b.toString)
  if let some n := expected then
    t.check s!"golden file count = {n}" (files.size == n) s!"(found {files.size})"
  let mut out := []
  for f in files do
    let name := f.fileName.getD f.toString
    let text ← IO.FS.readFile f
    match decodeProgramString text with
    | .error e => t.check s!"decode {name}" false s!"({e})"
    | .ok p =>
      -- 書き戻した JSON が元の JSON と一致 = 種別・演算子・子ノード・位置が保持されている。
      let orig := (Json.parse text).toOption.map Json.compress
      t.check s!"decode+roundtrip {name}" (orig == some p.toJson.compress)
      t.check s!"type check passes {name}" (match p.check with | .ok _ => true | .error _ => false)
      out := (name, p) :: out
  return out.reverse

def main (args : List String) : IO UInt32 := do
  let t : T := { fails := ← IO.mkRef 0 }
  let dir := args.headD "../lesdump/golden"
  let expected := (args.drop 1).head?.bind String.toNat?
  let progs ← goldenTests t dir expected
  let get (n : String) : Option Program := (progs.find? (·.1 == n)).map (·.2)

  -- 個別の構造確認（`force 50 + 60` は `(force 50) + 60`）
  match get "force-basic.json" with
  | some { body := [_, _, .varDecl _ "c" "" (.binary _ "+" (.force _ (.int _ 50)) (.int _ 60)), _], .. } =>
    t.check "force-basic: c = binary + (force 50) 60" true
  | _ => t.check "force-basic: c = binary + (force 50) 60" false
  match get "lazy-unused.json" with
  | some { analysis := { status := .ok, typeWarnings := [], .. },
           body := [.funcDef _ "choose" [⟨_, "first", "Int"⟩, ⟨_, "second", "Int"⟩] "Int" [.expr _ (.ident _ "first")],
                    .expr _ (.call _ (.ident _ "print") [.call _ (.ident _ "choose") [.int _ 42, .binary _ "/" (.int _ 1) (.int _ 0)]])] } =>
    t.check "lazy-unused: funcDef with annotated params, lazy 1/0 argument" true
  | _ => t.check "lazy-unused: funcDef with annotated params, lazy 1/0 argument" false
  match get "force-postfix-unused-arg.json" with
  | some { body := [_, .expr _ (.call _ _ [.call _ _ [_, .force _ (.binary _ "/" _ _)]])], .. } =>
    t.check "force-postfix-unused-arg: Force(Binary /)" true
  | _ => t.check "force-postfix-unused-arg: Force(Binary /)" false

  -- 整数は int64 に制約されない
  let big := okProgram ("[{\"kind\":\"ExprStmt\"," ++ p11 ++ ",\"expr\":{\"kind\":\"Int\"," ++ p11 ++ ",\"value\":123456789012345678901234567890}}]")
  match decodeProgramString big with
  | .ok { body := [.expr _ (.int _ v)], .. } => t.check "big integer beyond int64" (v == 123456789012345678901234567890)
  | _ => t.check "big integer beyond int64" false
  let neg := okProgram ("[{\"kind\":\"ExprStmt\"," ++ p11 ++ ",\"expr\":{\"kind\":\"Int\"," ++ p11 ++ ",\"value\":-5}}]")
  match decodeProgramString neg with
  | .ok { body := [.expr _ (.int _ v)], .. } => t.check "negative integer" (v == -5)
  | _ => t.check "negative integer" false

  -- 型エラーのプログラムはデコードできるが CheckedProgram にならない
  let bad := okProgram "[]" "type_error"
  match decodeProgramString bad with
  | .ok p =>
    t.check "type_error program keeps status" (p.analysis.status == .typeError)
    t.check "type_error program is not a CheckedProgram" (match p.check with | .ok _ => false | .error _ => true)
  | .error e => t.check "type_error program decodes" false s!"({e})"

  -- 拒否されるべき入力
  t.rejects "reject invalid JSON" "{" "invalid JSON"
  t.rejects "reject non-object JSON" "[]" "missing required field"
  t.rejects "reject unknown schema_version" ("{\"schema_version\":2,\"kind\":\"Program\",\"analysis\":{},\"body\":[]}") "unsupported schema_version 2"
  t.rejects "reject missing schema_version" ("{\"kind\":\"Program\",\"body\":[]}") "schema_version"
  t.rejects "reject wrong top-level kind" (("{\"schema_version\":1,\"kind\":\"Stmt\"}")) "expected kind 'Program'"
  t.rejects "reject unknown statement kind" (okProgram ("[{\"kind\":\"IfStmt\"," ++ p11 ++ "}]")) "unsupported statement kind 'IfStmt'"
  t.rejects "reject unknown expression kind"
    (okProgram ("[{\"kind\":\"ExprStmt\"," ++ p11 ++ ",\"expr\":{\"kind\":\"Float\"," ++ p11 ++ ",\"value\":1.5}}]")) "unsupported expression kind 'Float'"
  t.rejects "reject missing required field (Binary without op)"
    (okProgram ("[{\"kind\":\"ExprStmt\"," ++ p11 ++ ",\"expr\":{\"kind\":\"Binary\"," ++ p11 ++ ",\"left\":{\"kind\":\"Int\"," ++ p11 ++ ",\"value\":1},\"right\":{\"kind\":\"Int\"," ++ p11 ++ ",\"value\":2}}}]")) "missing required field 'op'"
  t.rejects "reject missing pos" (okProgram "[{\"kind\":\"ExprStmt\",\"expr\":{\"kind\":\"Int\",\"value\":1}}]") "missing required field 'pos'"
  t.rejects "reject wrong field type (name is a number)"
    (okProgram ("[{\"kind\":\"ExprStmt\"," ++ p11 ++ ",\"expr\":{\"kind\":\"Ident\"," ++ p11 ++ ",\"name\":3}}]")) "expected a string"
  t.rejects "reject non-integer Int value"
    (okProgram ("[{\"kind\":\"ExprStmt\"," ++ p11 ++ ",\"expr\":{\"kind\":\"Int\"," ++ p11 ++ ",\"value\":1.5}}]")) "expected an integer"
  t.rejects "reject unknown analysis status" (okProgram "[]" "maybe") "unknown analysis status 'maybe'"
  t.rejects "error message names the JSON location"
    (okProgram ("[{\"kind\":\"ExprStmt\"," ++ p11 ++ ",\"expr\":{\"kind\":\"Call\"," ++ p11 ++ ",\"callee\":{\"kind\":\"Ident\"," ++ p11 ++ ",\"name\":\"f\"},\"args\":[{\"kind\":\"Nope\"," ++ p11 ++ "}]}}]"))
    "body[0]: expr: args[0]: unsupported expression kind 'Nope'"

  let n ← t.fails.get
  IO.println (if n == 0 then "all Lean syntax tests passed" else s!"{n} Lean syntax test(s) FAILED")
  return (if n == 0 then 0 else 1)
