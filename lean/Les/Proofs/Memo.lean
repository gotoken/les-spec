import Les.Eval.Eval
import Les.Proofs.Heap

/-
P2b-1: 評価済み Cell を `whnf` で再強制しても何も変わらない（安定性）。
対象は `Les/Eval/Eval.lean` の既存の `whnf`。未評価（`suspended`）Cell を最初に強制する場合の
一般的な正しさ（メモ化の書き込みなど）は P2b-2 の対象で、ここでは扱わない。
`sorry` / `admit` / 新たな公理は使わない。
-/
namespace Les.Eval
open Les.Syntax

/-- `getHeap` は状態を変えずに現在の Heap を継続に渡す（定義から `rfl`）。 -/
theorem getHeap_bind {α : Type} (f : Heap → EvalM α) (m : Machine) :
    ((getHeap >>= f).run).run m = ((f m.heap).run).run m := rfl

/-- 実行が成功し、状態が `m'` になったなら、`bind` の続きは `m'` から `f v` を実行したものに等しい。 -/
theorem run_bind_ok {α β : Type} (x : EvalM α) (f : α → EvalM β) (m m' : Machine) (v : α)
    (hx : (x.run).run m = (Except.ok v, m')) :
    ((x >>= f).run).run m = ((f v).run).run m' := by
  simp only [ExceptT.run_bind, StateT.run_bind, hx]
  rfl

/-- fuel が 0 なら `whnf` は評価済みの Cell でも `outOfFuel` で止まる
    （だから下の定理は正の fuel `n + 1` を仮定する）。状態は変わらない。 -/
theorem whnf_zero (a : Addr) (m : Machine) :
    ((whnf 0 a).run).run m = (Except.error Halt.outOfFuel, m) := by
  rw [whnf]; rfl

/-- 1. 評価済み Cell `done v` を正の fuel で強制すると、結果は `ok v` で、Machine は実行前と完全に一致する。 -/
theorem whnf_done (n : Nat) (a : Addr) (v : Value) (m : Machine)
    (h : m.heap.cell? a = some (.done v)) :
    ((whnf (n + 1) a).run).run m = (Except.ok v, m) := by
  rw [whnf, getHeap_bind]
  simp [h]
  rfl

/-- 3. Machine 全体の等式から、stdout・Heap・Scope は変化しないことが導ける。 -/
theorem whnf_done_preserves (n : Nat) (a : Addr) (v : Value) (m m' : Machine)
    (h : m.heap.cell? a = some (.done v))
    (hrun : ((whnf (n + 1) a).run).run m = (Except.ok v, m')) :
    m'.stdout = m.stdout ∧ m'.heap = m.heap ∧ m'.heap.cells = m.heap.cells ∧
      m'.heap.scopes = m.heap.scopes := by
  have hm : m' = m := by
    have := whnf_done n a v m h
    rw [hrun] at this
    exact (Prod.mk.inj this).2
  subst hm
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- 2. 同じ評価済み Cell を 2 回続けて強制しても、値は同じで Machine は変化しない（fuel は別々でよい）。 -/
theorem whnf_done_twice (n k : Nat) (a : Addr) (v : Value) (m : Machine)
    (h : m.heap.cell? a = some (.done v)) :
    ((whnf (n + 1) a >>= fun v₁ => whnf (k + 1) a >>= fun v₂ => pure (v₁, v₂)).run).run m
      = (Except.ok (v, v), m) := by
  rw [run_bind_ok _ _ m m v (whnf_done n a v m h)]
  rw [run_bind_ok _ _ m m v (whnf_done k a v m h)]
  rfl

end Les.Eval
