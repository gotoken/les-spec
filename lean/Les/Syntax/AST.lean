/-
`lesdump`（lesdump/README.md、schema_version 1）が出力する AST を保持する型。
Go 側の AST のコピーではなく、現在のコーパスに必要な 9 種類のノードだけを持つ。
型注釈は未解釈の文字列のまま保持する（空文字列は「注釈なし」）。型推論器はここには無い。
-/
namespace Les.Syntax

/-- ソース位置（1 始まり）。 -/
structure Pos where
  line : Nat
  col : Nat
  deriving Repr, BEq, DecidableEq

/-- 式。`Int` は Lean の任意精度整数で、JSON の int64 に制約されない。 -/
inductive Expr where
  | ident (pos : Pos) (name : String)
  | int (pos : Pos) (value : Int)
  | str (pos : Pos) (value : String)
  | binary (pos : Pos) (op : String) (left right : Expr)
  /-- prefix `force` と postfix `!` はどちらもこのノード。 -/
  | force (pos : Pos) (expr : Expr)
  | call (pos : Pos) (callee : Expr) (args : List Expr)
  deriving Repr, BEq

/-- 関数パラメーター（`typeAnnot` が空なら注釈なし）。 -/
structure Param where
  pos : Pos
  name : String
  typeAnnot : String
  deriving Repr, BEq

inductive Stmt where
  | expr (pos : Pos) (e : Expr)
  | varDecl (pos : Pos) (name typeAnnot : String) (value : Expr)
  | funcDef (pos : Pos) (name : String) (params : List Param) (returnType : String) (body : List Stmt)
  deriving Repr, BEq

/-- Go の型推論の結果。 -/
inductive Status where
  | ok
  | typeError
  deriving Repr, BEq, DecidableEq

structure Analysis where
  status : Status
  typeError : String
  typeWarnings : List String
  deriving Repr, BEq

/-- デコード直後のプログラム。型エラーのものも含むので、そのまま評価してはいけない。 -/
structure Program where
  analysis : Analysis
  body : List Stmt
  deriving Repr, BEq

/-- 型検査を通った（`analysis.status = ok`）プログラム。後の評価器はこれだけを受け取る。 -/
structure CheckedProgram where
  program : Program
  ok : program.analysis.status = Status.ok

/-- 型エラーのプログラムは `CheckedProgram` にならない。 -/
def Program.check (p : Program) : Except String CheckedProgram :=
  if h : p.analysis.status = Status.ok then
    .ok ⟨p, h⟩
  else
    .error s!"program has a type error: {p.analysis.typeError}"

end Les.Syntax
