import Les.Eval.Types

/- Heap・スコープの基本操作。すべて全域（`partial` なし）。 -/
namespace Les.Eval
open Les.Syntax

def Heap.alloc (h : Heap) (c : Cell) : Heap × Addr :=
  ({ h with cells := h.cells.push c }, h.cells.size)

def Heap.cell? (h : Heap) (a : Addr) : Option Cell := h.cells[a]?

def Heap.setCell (h : Heap) (a : Addr) (c : Cell) : Heap :=
  { h with cells := h.cells.set! a c }

def Heap.newScope (h : Heap) (parent : Option ScopeId) : Heap × ScopeId :=
  ({ h with scopes := h.scopes.push { vars := [], parent } }, h.scopes.size)

/-- スコープ自身の「現在の」束縛だけを見る（再束縛の判定: E3）。 -/
def Heap.lookupLocal (h : Heap) (s : ScopeId) (n : String) : Option Addr :=
  match h.scopes[s]? with
  | some sc => (sc.vars.find? (·.1 == n)).map (·.2)
  | none => none

/-- 親へたどる探索。深さは `scopes.size` で抑える（サイクルがあっても停止）。 -/
def Heap.lookupFrom (h : Heap) : Nat → ScopeId → String → Option Addr
  | 0, _, _ => none
  | fuel + 1, s, n =>
    match h.lookupLocal s n with
    | some a => some a
    | none =>
      match h.scopes[s]? with
      | some { parent := some p, .. } => h.lookupFrom fuel p n
      | _ => none

def Heap.lookup (h : Heap) (s : ScopeId) (n : String) : Option Addr :=
  h.lookupFrom (h.scopes.size + 1) s n

/-- 束縛の追加または置き換え（再束縛は同じ位置を置き換える）。 -/
def Heap.bind (h : Heap) (s : ScopeId) (n : String) (a : Addr) : Heap :=
  match h.scopes[s]? with
  | none => h
  | some sc =>
    let vars :=
      if sc.vars.any (·.1 == n) then sc.vars.map (fun p => if p.1 == n then (n, a) else p)
      else sc.vars ++ [(n, a)]
    { h with scopes := h.scopes.set! s { sc with vars } }

/-- 空のヒープ。スコープ 0 = 組込み（print, exit）、スコープ 1 = プログラムのグローバル。 -/
def Heap.initial : Heap :=
  let h : Heap := { cells := #[], scopes := #[] }
  let (h, root) := h.newScope none
  let (h, pa) := h.alloc (.done (.builtin .print))
  let (h, ea) := h.alloc (.done (.builtin .exit))
  let h := (h.bind root "print" pa).bind root "exit" ea
  let (h, _) := h.newScope (some root)
  h

def globalScope : ScopeId := 1

mutual
/-- 式に現れる名前（過大近似でよい: 設計メモ 2.2）。 -/
def exprNames : Expr → List String
  | .ident _ n => [n]
  | .int _ _ => []
  | .str _ _ => []
  | .binary _ _ l r => exprNames l ++ exprNames r
  | .force _ e => exprNames e
  | .call _ c args => exprNames c ++ namesList args
def namesList : List Expr → List String
  | [] => []
  | e :: es => exprNames e ++ namesList es
end

def exprPos : Expr → Pos
  | .ident p _ | .int p _ | .str p _ | .binary p .. | .force p _ | .call p .. => p

def stmtPos : Stmt → Pos
  | .expr p _ | .varDecl p .. | .funcDef p .. => p

end Les.Eval
