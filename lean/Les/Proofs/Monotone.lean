import Les.Eval.Eval
import Les.Proofs.Heap

/-
P2d-2: `cells.size` の非減少性のための基本補題。対象は既存の `Heap` 操作と `EvalM` の基本操作。
`demand` / `evalE` / `whnf` の再帰全体の単調性はこのファイルでは扱わず、
P2d-3 の `MonotoneEval.lean` でこれらの補題を組み合わせて証明済み。
`sorry` / `admit` / 新たな公理は使わない。
-/
namespace Les.Eval
open Les.Syntax

/-! ## 1. 状態の関係 -/

/-- Machine の Cell 数が非減少: `m` から `m'` へ。 -/
def Machine.CellsMono (m m' : Machine) : Prop := m.heap.cells.size ≤ m'.heap.cells.size

theorem Machine.CellsMono.refl (m : Machine) : m.CellsMono m := Nat.le_refl _

theorem Machine.CellsMono.trans {m₁ m₂ m₃ : Machine} (h₁ : m₁.CellsMono m₂) (h₂ : m₂.CellsMono m₃) :
    m₁.CellsMono m₃ := Nat.le_trans h₁ h₂

/-- 評価の前後（成功・例外のどちらでも）で Cell 数が非減少: 最終状態だけを見る。 -/
def Mono {α : Type} (x : EvalM α) : Prop :=
  ∀ m : Machine, m.CellsMono ((x.run).run m).2

/-! ## 2. Heap の基本操作 -/

theorem Heap.alloc_size (h : Heap) (c : Cell) : (h.alloc c).1.cells.size = h.cells.size + 1 := by
  simp [Heap.alloc]

theorem Heap.newScope_cells (h : Heap) (p : Option ScopeId) :
    (h.newScope p).1.cells = h.cells := rfl

theorem Heap.newScope_cells_size (h : Heap) (p : Option ScopeId) :
    (h.newScope p).1.cells.size = h.cells.size := rfl

/-! ## 3. `EvalM` の `bind` などの合成補題 -/

theorem mono_pure {α : Type} (a : α) : Mono (pure a : EvalM α) := fun _ => Nat.le_refl _

/-- 例外は状態を変えない（`ExceptT` の下に `StateM` があるので、`throw` までの状態変更は残る）。 -/
theorem mono_throw {α : Type} (e : Halt) : Mono (throw e : EvalM α) := fun _ => Nat.le_refl _

/-- 前半と後半がともに非減少なら合成も非減少。前半が例外で終わる場合は後半が走らず、
    前半までの状態変更がそのまま最終状態になる。 -/
theorem mono_bind {α β : Type} {x : EvalM α} {f : α → EvalM β}
    (hx : Mono x) (hf : ∀ a, Mono (f a)) : Mono (x >>= f) := by
  intro m
  have hx' := hx m
  simp only [ExceptT.run_bind, StateT.run_bind]
  generalize hr : (x.run).run m = r at hx' ⊢
  obtain ⟨res, m'⟩ := r
  cases res with
  | error e => exact hx'
  | ok v => exact Nat.le_trans hx' (hf v m')

/-- `tryCatch`: 本体が非減少で、ハンドラも（どの例外でも）非減少なら全体も非減少。
    評価器の `tryCatch ... (throw (h.attach p))` は状態を変えずに投げ直す。 -/
theorem mono_tryCatch {α : Type} {x : EvalM α} {handler : Halt → EvalM α}
    (hx : Mono x) (hh : ∀ e, Mono (handler e)) : Mono (tryCatch x handler) := by
  intro m
  have hx' := hx m
  have key : ((tryCatch x handler).run).run m =
      (match (StateT.run x m : Except Halt α × Machine) with
        | (Except.ok a, m') => (Except.ok a, m')
        | (Except.error e, m') => ((handler e).run).run m') := by
    show (ExceptT.tryCatch x handler).run.run m = _
    simp only [ExceptT.tryCatch, ExceptT.run, ExceptT.mk, StateT.run_bind]
    generalize StateT.run x m = r
    obtain ⟨res, m'⟩ := r
    cases res <;> rfl
  rw [key]
  have hx2 : m.CellsMono (StateT.run x m).2 := hx'
  generalize StateT.run x m = r at hx2 ⊢
  obtain ⟨res, m'⟩ := r
  cases res with
  | ok v => exact hx2
  | error e => exact Nat.le_trans hx2 (hh e m')

/-- 例外を同じ形で付け替えて投げ直すハンドラ（評価器の `h.attach p`）は非減少。 -/
theorem mono_rethrow_attach {α : Type} (p : Pos) : ∀ e : Halt, Mono (throw (e.attach p) : EvalM α) :=
  fun _ => mono_throw _

/-! ## 4. 評価器が使う基本的な状態操作 -/

theorem mono_getHeap : Mono getHeap := fun _ => Nat.le_refl _

/-- `modHeap f` は、`f` が Cell 数を減らさないときに限り非減少と言える。 -/
theorem mono_modHeap (f : Heap → Heap) (hf : ∀ h, h.cells.size ≤ (f h).cells.size) :
    Mono (modHeap f) := fun m => hf m.heap

/-- 反例（記録用）: `f` が Cell を全部捨てる関数なら、`modHeap f` は単調ではない。 -/
theorem modHeap_not_mono :
    ¬ (∀ f : Heap → Heap, Mono (modHeap f)) := by
  intro h
  have := h (fun hp => { hp with cells := #[] }) { heap := { cells := #[Cell.done .unit], scopes := #[] }, stdout := "" }
  have h2 : ((modHeap (fun hp : Heap => { hp with cells := #[] })).run.run
      { heap := { cells := #[Cell.done .unit], scopes := #[] }, stdout := "" }).2.heap.cells.size = 0 := rfl
  unfold Machine.CellsMono at this
  rw [h2] at this
  exact absurd this (by decide)

/-- `alloc` は 1 増える（単調）。 -/
theorem mono_alloc (c : Cell) : Mono (alloc c) := by
  intro m
  show m.heap.cells.size ≤ (m.heap.alloc c).1.cells.size
  rw [Heap.alloc_size]; exact Nat.le_succ _

/-- `alloc` の実行後の Cell 数はちょうど +1（単調性より強い）。 -/
theorem alloc_cells_size (c : Cell) (m : Machine) :
    ((((alloc c).run).run m).2).heap.cells.size = m.heap.cells.size + 1 := by
  show (m.heap.alloc c).1.cells.size = _
  exact Heap.alloc_size _ _

/-- `modHeap` の具体的な使い方: `setCell` / `bind` は Cell 数を変えないので単調。 -/
theorem mono_modHeap_setCell (a : Addr) (c : Cell) : Mono (modHeap (·.setCell a c)) :=
  mono_modHeap _ fun h => by rw [Heap.setCell_size]; exact Nat.le_refl _

theorem mono_modHeap_bind (s : ScopeId) (n : String) (a : Addr) : Mono (modHeap (·.bind s n a)) :=
  mono_modHeap _ fun h => by rw [Heap.bind_cells]; exact Nat.le_refl _

/-- stdout への追記（`print`）。Heap は変わらない。 -/
theorem mono_modify_stdout (s : String) :
    Mono (modify fun m => { m with stdout := m.stdout ++ s } : EvalM Unit) := fun _ => Nat.le_refl _

/-- `callClosure` が使う「新しいスコープを作る」操作（`modifyGet`）。Cell 数は変わらない。 -/
theorem mono_newScope (parent : Option ScopeId) :
    Mono (modifyGet fun m =>
      let (h, sc) := m.heap.newScope parent
      (sc, { m with heap := h }) : EvalM ScopeId) := fun m => by
  show m.heap.cells.size ≤ (m.heap.newScope parent).1.cells.size
  rw [Heap.newScope_cells_size]; exact Nat.le_refl _

/-! ## 5. 有効なアドレスの保存 -/

/-- 非減少な状態遷移では、有効なアドレスは有効なまま。 -/
theorem Machine.CellsMono.validAddr {m m' : Machine} (hm : m.CellsMono m') {a : Addr}
    (ha : m.heap.ValidAddr a) : m'.heap.ValidAddr a :=
  Nat.lt_of_lt_of_le ha hm

/-- 評価開始時に有効なアドレスは、`Mono` な処理の終了時（成功でも例外でも）にも有効。 -/
theorem mono_validAddr {α : Type} {x : EvalM α} (hx : Mono x) (m : Machine) {a : Addr}
    (ha : m.heap.ValidAddr a) : (((x.run).run m).2).heap.ValidAddr a :=
  (hx m).validAddr ha

/-! ## 6. 合成の使用例（評価器の `varDecl` 末尾に似た列、途中で例外が起きる場合を含む） -/

/-- `alloc` → `bind` → 例外 の列。例外で終わっても Cell 数は減らず、開始時に有効だったアドレスは有効なまま。 -/
theorem mono_example_alloc_bind_throw (c : Cell) (s : ScopeId) (n : String) (e : Halt) :
    Mono (do let a ← alloc c; modHeap (·.bind s n a); (throw e : EvalM Unit)) :=
  mono_bind (mono_alloc c) fun a =>
    mono_bind (mono_modHeap_bind s n a) fun _ => mono_throw e

theorem example_validAddr_preserved (c : Cell) (s : ScopeId) (n : String) (e : Halt) (m : Machine)
    {a : Addr} (ha : m.heap.ValidAddr a) :
    (((do let a ← alloc c; modHeap (·.bind s n a); (throw e : EvalM Unit)).run).run m).2.heap.ValidAddr a :=
  mono_validAddr (mono_example_alloc_bind_throw c s n e) m ha

end Les.Eval
