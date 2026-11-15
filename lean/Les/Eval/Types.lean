import Les.Syntax

/-
段階 A の評価器のデータ型（docs/evaluator-design.md 3 節）。
設計メモからの差分は `Halt.unsupported` の追加だけ（未対応の機構に当たったことを
「エラー」と区別して報告するため。比較では PASS にならない）。
-/
namespace Les.Eval
open Les.Syntax

abbrev Addr := Nat
abbrev ScopeId := Nat

inductive Builtin where
  | print
  | exit
  deriving Repr, BEq

inductive Value where
  | int (i : Int)
  | str (s : String)
  | unit
  | builtin (b : Builtin)
  /-- `def`。段階 A では作られない（`funcDef` は unsupported）。型だけ設計どおり置く。 -/
  | closure (params : List Param) (body : List Stmt) (scope : ScopeId)
  deriving Repr

/-- Thunk の環境。`snap` が先、無ければ `scope` の「現在の」中身（E14, E15）。 -/
structure Env where
  snap : List (String × Addr)
  scope : ScopeId
  deriving Repr

inductive Cell where
  | done (v : Value)
  | suspended (e : Expr) (env : Env)
  | blackhole (e : Expr)
  deriving Repr

structure Scope where
  vars : List (String × Addr)
  parent : Option ScopeId
  deriving Repr

structure Heap where
  cells : Array Cell
  scopes : Array Scope
  deriving Repr

inductive ErrPos where
  | pending
  | absent
  | at (p : Pos)
  deriving Repr, BEq

inductive Halt where
  | exit (code : Int)
  | error (msg : String) (pos : ErrPos)
  /-- 段階 A が扱わない機構（def・呼び出し・未観測の演算）。Go との比較では UNSUPPORTED。 -/
  | unsupported (what : String)
  | outOfFuel
  deriving Repr

structure Machine where
  heap : Heap
  stdout : String
  deriving Repr

abbrev EvalM := ExceptT Halt (StateM Machine)

structure Outcome where
  stdout : String
  halt : Option Halt
  deriving Repr

end Les.Eval
