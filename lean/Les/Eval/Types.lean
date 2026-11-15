import Les.Syntax

/-
P1c-4 の段階 A で導入し、P1c-5 の段階 B でも利用する評価器のデータ型
（docs/evaluator-design.md 3 節）。
`Halt.unsupported` は、現在も評価器が扱わない演算・呼び出し等を通常の実行時エラーと区別する。
差分テストでは UNSUPPORTED は PASS にならない。
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
  /-- `def` の実行時表現。段階 B では `funcDef` と `callClosure` が生成・呼び出しを行う。 -/
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
  /-- 現在の評価器が未対応の演算・引数形式など。Go との比較では UNSUPPORTED（非 PASS）。 -/
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
