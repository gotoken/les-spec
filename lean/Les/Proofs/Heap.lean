import Les.Eval.Heap

/-
P2a: `Heap` の基本操作に関する補題。対象は `Les/Eval/Heap.lean` の既存の定義そのもの
（証明用の別実装ではない）。`sorry` / `admit` / 新たな公理は使わない。
アドレスの有効性（`a < h.cells.size`）は各命題の仮定として明示する。
-/
namespace Les.Eval
open Les.Syntax

/-- 有効なアドレス: Cell の配列の範囲内。 -/
def Heap.ValidAddr (h : Heap) (a : Addr) : Prop := a < h.cells.size

/-! ## 1. `Heap.alloc` -/

/-- `alloc` は新しいアドレスとして古い `cells.size` を返す。 -/
theorem Heap.alloc_addr (h : Heap) (c : Cell) : (h.alloc c).2 = h.cells.size := rfl

/-- `alloc` は既存の（有効な）アドレスの Cell を変更しない。 -/
theorem Heap.alloc_cell?_of_valid (h : Heap) (c : Cell) {a : Addr} (ha : h.ValidAddr a) :
    (h.alloc c).1.cell? a = h.cell? a := by
  unfold Heap.alloc Heap.cell? Heap.ValidAddr at *
  simp [Array.getElem?_push, Nat.ne_of_lt ha]

/-- 新しいアドレスには `c` が入る。 -/
theorem Heap.alloc_cell?_new (h : Heap) (c : Cell) :
    (h.alloc c).1.cell? (h.alloc c).2 = some c := by
  simp [Heap.alloc, Heap.cell?]

/-- `alloc` で有効なアドレスは保たれる（増える）。 -/
theorem Heap.alloc_validAddr (h : Heap) (c : Cell) {a : Addr} (ha : h.ValidAddr a) :
    (h.alloc c).1.ValidAddr a := by
  have ha' : a < h.cells.size := ha
  show a < (h.cells.push c).size
  rw [Array.size_push]; exact Nat.lt_succ_of_lt ha'

/-- `alloc` は Scope を変更しない。 -/
theorem Heap.alloc_scopes (h : Heap) (c : Cell) : (h.alloc c).1.scopes = h.scopes := rfl

/-! ## 2. `Heap.setCell` -/

/-- `setCell` は更新対象と異なるアドレスの Cell を変更しない。
    （有効性の仮定は不要: 範囲外の `set!` は何もしないので、`b` が有効かどうかによらず成り立つ。） -/
theorem Heap.setCell_cell?_ne (h : Heap) (a : Addr) (c : Cell) {b : Addr} (hne : a ≠ b) :
    (h.setCell a c).cell? b = h.cell? b := by
  unfold Heap.setCell Heap.cell?
  simp [Array.set!_eq_setIfInBounds, hne]

/-- 有効なアドレスを更新すると、その Cell は `c` になる。 -/
theorem Heap.setCell_cell?_self (h : Heap) (c : Cell) {a : Addr} (ha : h.ValidAddr a) :
    (h.setCell a c).cell? a = some c := by
  unfold Heap.setCell Heap.cell? Heap.ValidAddr at *
  simp [Array.set!_eq_setIfInBounds, ha]

/-- `setCell` は Cell の個数を変えず、有効なアドレスの集合は変わらない。 -/
theorem Heap.setCell_size (h : Heap) (a : Addr) (c : Cell) :
    (h.setCell a c).cells.size = h.cells.size := by
  simp [Heap.setCell]

theorem Heap.setCell_validAddr (h : Heap) (a : Addr) (c : Cell) {b : Addr} (hb : h.ValidAddr b) :
    (h.setCell a c).ValidAddr b := by
  unfold Heap.ValidAddr at *
  rw [Heap.setCell_size]; exact hb

/-- `setCell` は Scope を変更しない。 -/
theorem Heap.setCell_scopes (h : Heap) (a : Addr) (c : Cell) :
    (h.setCell a c).scopes = h.scopes := rfl

/-! ## 3. `Heap.bind` -/

/-- `bind` は Cell の配列そのものを変更しない。 -/
theorem Heap.bind_cells (h : Heap) (s : ScopeId) (n : String) (a : Addr) :
    (h.bind s n a).cells = h.cells := by
  unfold Heap.bind
  split <;> rfl

/-- したがって、どのアドレスの Cell も変わらない（有効性の仮定は不要）。 -/
theorem Heap.bind_cell? (h : Heap) (s : ScopeId) (n : String) (a b : Addr) :
    (h.bind s n a).cell? b = h.cell? b := by
  unfold Heap.cell?
  rw [Heap.bind_cells]

theorem Heap.bind_validAddr (h : Heap) (s : ScopeId) (n : String) (a : Addr) {b : Addr}
    (hb : h.ValidAddr b) : (h.bind s n a).ValidAddr b := by
  unfold Heap.ValidAddr at *
  rw [Heap.bind_cells]; exact hb

/-- `bind` は Scope の個数を変えない。 -/
theorem Heap.bind_scopes_size (h : Heap) (s : ScopeId) (n : String) (a : Addr) :
    (h.bind s n a).scopes.size = h.scopes.size := by
  unfold Heap.bind
  split <;> simp

private theorem find_replace (vs : List (String × Addr)) (n : String) (a : Addr)
    (h : vs.any (·.1 == n) = true) :
    (vs.map (fun p => if p.1 == n then (n, a) else p)).find? (·.1 == n) = some (n, a) := by
  induction vs with
  | nil => simp at h
  | cons p ps ih =>
    by_cases hp : (p.1 == n) = true
    · simp only [List.map_cons, if_pos hp, List.find?_cons, beq_self_eq_true]
    · have hf : (p.1 == n) = false := by simpa using hp
      have hps : ps.any (·.1 == n) = true := by
        simpa [hf] using h
      simp only [List.map_cons, hf, Bool.false_eq_true, if_false, List.find?_cons]
      exact ih hps

private theorem find_append_new (vs : List (String × Addr)) (n : String) (a : Addr)
    (h : ¬ vs.any (·.1 == n) = true) : (vs ++ [(n, a)]).find? (·.1 == n) = some (n, a) := by
  induction vs with
  | nil => simp
  | cons p ps ih =>
    have hp : ¬ (p.1 == n) = true := fun hh => h (by simp [hh])
    have hps : ¬ ps.any (·.1 == n) = true := fun hh => h (by simp [hh])
    simp [hp, ih hps]

/-- 束縛先のスコープが存在すれば、`bind` の直後にその名前は `a` を指す。
    （`bind` が Cell ではなく名前の対応を変える操作であることの確認。）
    追加・置き換えの 2 通りがあるので、`vars` の場合分けで示す。 -/
theorem Heap.bind_lookupLocal_self (h : Heap) (s : ScopeId) (n : String) (a : Addr)
    (hs : s < h.scopes.size) : (h.bind s n a).lookupLocal s n = some a := by
  unfold Heap.bind Heap.lookupLocal
  have hget : h.scopes[s]? = some h.scopes[s] := by simp [hs]
  rw [hget]
  simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, if_pos hs]
  generalize (h.scopes[s]).vars = vs
  by_cases hany : vs.any (·.1 == n) = true
  · simp only [if_true, if_pos hany, find_replace vs n a hany, Option.map]
  · simp only [if_true, if_neg hany, find_append_new vs n a hany, Option.map]

end Les.Eval
