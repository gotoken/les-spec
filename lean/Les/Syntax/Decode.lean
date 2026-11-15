import Lean.Data.Json
import Les.Syntax.AST

/-
`lesdump` の JSON から `Les.Syntax.Program` へのデコーダー。標準ライブラリ（`Lean.Data.Json`）のみ使用。
不明な `schema_version`、未対応の `kind`、必須フィールドの欠落・型違いはすべて明示的なエラー
（エラー文頭に `body[1].expr.args[0]` のような JSON 上の場所を付ける）。
`partial def` を使うのは JSON の入れ子を再帰で辿るため。終了性の証明は後段で必要になれば行う。
-/
namespace Les.Syntax
open Lean (Json)

/-- 対応する `lesdump` のスキーマバージョン。 -/
def supportedSchemaVersion : Nat := 1

abbrev Decode (α : Type) := Except String α

private def at_ (ctx : String) (r : Decode α) : Decode α :=
  r.mapError fun e => if ctx.isEmpty then e else s!"{ctx}: {e}"

private def field (j : Json) (name : String) : Decode Json :=
  match j.getObjVal? name with
  | .ok v => .ok v
  | .error _ => .error s!"missing required field '{name}'"

private def strOf (j : Json) : Decode String :=
  j.getStr?.mapError fun _ => "expected a string"

private def natOf (j : Json) : Decode Nat :=
  j.getNat?.mapError fun _ => "expected a non-negative integer"

private def intOf (j : Json) : Decode Int :=
  j.getInt?.mapError fun _ => "expected an integer"

private def arrOf (j : Json) : Decode (Array Json) :=
  j.getArr?.mapError fun _ => "expected an array"

private def strField (j : Json) (name : String) : Decode String :=
  at_ name (field j name >>= strOf)

private def listOf (name : String) (j : Json) (f : Json → Decode α) : Decode (List α) := do
  let arr ← at_ name (field j name >>= arrOf)
  let mut out := #[]
  for h : i in [0:arr.size] do
    out := out.push (← at_ s!"{name}[{i}]" (f arr[i]))
  return out.toList

def decodePos (j : Json) : Decode Pos := do
  let p ← field j "pos"
  at_ "pos" do
    return { line := ← (field p "line" >>= natOf), col := ← (field p "col" >>= natOf) }

partial def decodeExpr (j : Json) : Decode Expr := do
  let kind ← strField j "kind"
  let pos ← decodePos j
  let sub (name : String) : Decode Expr := at_ name (field j name >>= decodeExpr)
  match kind with
  | "Ident" => return .ident pos (← strField j "name")
  | "Int" => return .int pos (← at_ "value" (field j "value" >>= intOf))
  | "String" => return .str pos (← strField j "value")
  | "Binary" => return .binary pos (← strField j "op") (← sub "left") (← sub "right")
  | "Force" => return .force pos (← sub "expr")
  | "Call" => return .call pos (← sub "callee") (← listOf "args" j decodeExpr)
  | k => throw s!"unsupported expression kind '{k}'"

private def decodeParam (j : Json) : Decode Param := do
  return { pos := ← decodePos j, name := ← strField j "name", typeAnnot := ← strField j "type_annot" }

partial def decodeStmt (j : Json) : Decode Stmt := do
  let kind ← strField j "kind"
  let pos ← decodePos j
  match kind with
  | "ExprStmt" => return .expr pos (← at_ "expr" (field j "expr" >>= decodeExpr))
  | "VarDecl" =>
    return .varDecl pos (← strField j "name") (← strField j "type_annot")
      (← at_ "value" (field j "value" >>= decodeExpr))
  | "FuncDef" =>
    return .funcDef pos (← strField j "name") (← listOf "params" j decodeParam)
      (← strField j "return_type") (← listOf "body" j decodeStmt)
  | k => throw s!"unsupported statement kind '{k}'"

private def decodeAnalysis (j : Json) : Decode Analysis := do
  let status ← match (← strField j "status") with
    | "ok" => pure Status.ok
    | "type_error" => pure Status.typeError
    | s => throw s!"status: unknown analysis status '{s}'"
  let warnings ← at_ "type_warnings" do
    (← (field j "type_warnings" >>= arrOf)).toList.mapM strOf
  return { status, typeError := ← strField j "type_error", typeWarnings := warnings }

def decodeProgram (j : Json) : Decode Program := do
  let version ← at_ "schema_version" (field j "schema_version" >>= natOf)
  unless version == supportedSchemaVersion do
    throw s!"unsupported schema_version {version} (this decoder supports {supportedSchemaVersion})"
  let kind ← strField j "kind"
  unless kind == "Program" do
    throw s!"expected kind 'Program', got '{kind}'"
  return {
    analysis := ← at_ "analysis" (field j "analysis" >>= decodeAnalysis)
    body := ← listOf "body" j decodeStmt }

/-- JSON 文字列から読み込む。不正な JSON も `Except.error`。 -/
def decodeProgramString (s : String) : Decode Program := do
  let j ← (Json.parse s).mapError fun e => s!"invalid JSON: {e}"
  decodeProgram j

end Les.Syntax
