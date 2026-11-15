import Lean.Data.Json
import Les.Syntax.AST
import Les.Syntax.Decode

/-
AST を `lesdump` と同じ JSON 形式に書き戻す。主にテスト用: golden を読み込んで書き戻した結果が
元の JSON と一致すれば、ノード種別・演算子・子ノードの構造・位置が保持されていると言える。
-/
namespace Les.Syntax
open Lean (Json)

private def obj (kvs : List (String × Json)) : Json := Json.mkObj kvs

def Pos.toJson (p : Pos) : Json := obj [("line", p.line), ("col", p.col)]

partial def Expr.toJson : Expr → Json
  | .ident p n => obj [("kind", "Ident"), ("pos", p.toJson), ("name", n)]
  | .int p v => obj [("kind", "Int"), ("pos", p.toJson), ("value", Json.num (Lean.JsonNumber.fromInt v))]
  | .str p v => obj [("kind", "String"), ("pos", p.toJson), ("value", v)]
  | .binary p op l r =>
    obj [("kind", "Binary"), ("pos", p.toJson), ("op", op), ("left", l.toJson), ("right", r.toJson)]
  | .force p e => obj [("kind", "Force"), ("pos", p.toJson), ("expr", e.toJson)]
  | .call p c args =>
    obj [("kind", "Call"), ("pos", p.toJson), ("callee", c.toJson),
         ("args", Json.arr (args.map Expr.toJson).toArray)]

def Param.toJson (p : Param) : Json :=
  obj [("name", p.name), ("type_annot", p.typeAnnot), ("pos", p.pos.toJson)]

partial def Stmt.toJson : Stmt → Json
  | .expr p e => obj [("kind", "ExprStmt"), ("pos", p.toJson), ("expr", e.toJson)]
  | .varDecl p n t v =>
    obj [("kind", "VarDecl"), ("pos", p.toJson), ("name", n), ("type_annot", t), ("value", v.toJson)]
  | .funcDef p n ps r b =>
    obj [("kind", "FuncDef"), ("pos", p.toJson), ("name", n),
         ("params", Json.arr (ps.map Param.toJson).toArray), ("return_type", r),
         ("body", Json.arr (b.map Stmt.toJson).toArray)]

def Analysis.toJson (a : Analysis) : Json :=
  obj [("status", match a.status with | .ok => "ok" | .typeError => "type_error"),
       ("type_error", a.typeError),
       ("type_warnings", Json.arr (a.typeWarnings.map (Json.str ·)).toArray)]

def Program.toJson (p : Program) : Json :=
  obj [("schema_version", supportedSchemaVersion), ("kind", "Program"),
       ("analysis", p.analysis.toJson), ("body", Json.arr (p.body.map Stmt.toJson).toArray)]

end Les.Syntax
