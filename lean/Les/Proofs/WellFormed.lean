import Les.Eval.Heap
import Les.Proofs.Heap
import Les.Proofs.Capture

/-
P2d-1: Heap の**構造的**な整合性 `Heap.StructWF` と、基本操作による保存性。
対象は `Les/Eval/Heap.lean` の既存の定義（変更しない）。`sorry` / `admit` / 新たな公理は使わない。

**`StructWF` が検証するのは次の 3 つだけ**で、Heap の完全な整合性ではない:
  1. `VarsValid`: `Scope.vars` のアドレスは `cells` の範囲内（有効）。
  2. `ParentsValid`: `Scope.parent = some p` なら `p` は `scopes` の範囲内。
  3. `ParentsDecreasing`: `Scope.parent = some p` なら `p < s`（スコープ参照が循環しないための
     **十分条件**。`Heap.newScope` が親を先に作る使い方に対応する。循環の必要十分な特徴づけではない）。
含まない: `Cell.suspended` の `Env.snap` / `Env.scope`、`Cell.blackhole`、`Value.closure` の捕捉スコープが
指す参照の有効性、`Cell` の内容に関する不変条件、`demand` / `evalE` の実行を通した保存。
-/
namespace Les.Eval
open Les.Syntax

/-- 1. `Scope.vars` に登録されたアドレスが有効な Cell を指す。 -/
def Heap.VarsValid (h : Heap) : Prop :=
  ∀ (s : ScopeId) (sc : Scope), h.scopes[s]? = some sc → ∀ p ∈ sc.vars, h.ValidAddr p.2

/-- 2. `Scope.parent` が存在するなら、参照先スコープが存在する。 -/
def Heap.ParentsValid (h : Heap) : Prop :=
  ∀ (s : ScopeId) (sc : Scope) (p : ScopeId), h.scopes[s]? = some sc → sc.parent = some p →
    p < h.scopes.size

/-- 3. 親は自分より前に作られたスコープ（添字が小さい）。循環しないための十分条件。 -/
def Heap.ParentsDecreasing (h : Heap) : Prop :=
  ∀ (s : ScopeId) (sc : Scope) (p : ScopeId), h.scopes[s]? = some sc → sc.parent = some p → p < s

/-- 構造的整合性（上の 3 つの組。完全な Heap 整合性ではない）。 -/
def Heap.StructWF (h : Heap) : Prop := h.VarsValid ∧ h.ParentsValid ∧ h.ParentsDecreasing

/-! ## `Heap.initial` -/

/-- `Heap.initial` の具体的な値（定義から `rfl`）。 -/
theorem Heap.initial_eq : Heap.initial =
    { cells := #[.done (.builtin .print), .done (.builtin .exit)],
      scopes := #[{ vars := [("print", 0), ("exit", 1)], parent := none },
                  { vars := [], parent := some 0 }] } := rfl

theorem Heap.initial_structWF : Heap.initial.StructWF := by
  rw [Heap.initial_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro s sc hs p hp
    rcases s with _ | _ | s
    · simp at hs; subst hs; simp at hp; rcases hp with rfl | rfl <;> simp [Heap.ValidAddr]
    · simp at hs; subst hs; simp at hp
    · simp at hs
  · intro s sc p hs hp
    rcases s with _ | _ | s
    · simp at hs; subst hs; simp at hp
    · simp at hs; subst hs; simp at hp; subst hp; simp
    · simp at hs
  · intro s sc p hs hp
    rcases s with _ | _ | s
    · simp at hs; subst hs; simp at hp
    · simp at hs; subst hs; simp at hp; subst hp; simp
    · simp at hs


/-! ## `Heap.alloc` / `Heap.setCell`（Scope を変えない操作） -/

/-- `alloc` は Scope を変えず Cell を増やすだけなので、構造的整合性を保存する（仮定は `StructWF`）。 -/
theorem Heap.alloc_structWF (h : Heap) (c : Cell) (hwf : h.StructWF) : (h.alloc c).1.StructWF := by
  obtain ⟨hv, hp, hd⟩ := hwf
  have hs : (h.alloc c).1.scopes = h.scopes := Heap.alloc_scopes h c
  refine ⟨?_, ?_, ?_⟩
  · intro s sc hsc q hq
    rw [hs] at hsc
    exact Heap.alloc_validAddr h c (hv s sc hsc q hq)
  · intro s sc q hsc hq
    rw [hs] at hsc ⊢
    exact hp s sc q hsc hq
  · intro s sc q hsc hq
    rw [hs] at hsc
    exact hd s sc q hsc hq

/-- `setCell` は Scope も Cell の個数も変えないので、構造的整合性を保存する。
    **注意**: `StructWF` は Cell の*内容*を含まない。Cell 内の参照（`Env.snap`・`Value.closure` の
    スコープなど）まで整合性に含める場合は、書き込む Cell の参照が有効であるという別の仮定が要る。 -/
theorem Heap.setCell_structWF (h : Heap) (a : Addr) (c : Cell) (hwf : h.StructWF) :
    (h.setCell a c).StructWF := by
  obtain ⟨hv, hp, hd⟩ := hwf
  have hs : (h.setCell a c).scopes = h.scopes := Heap.setCell_scopes h a c
  refine ⟨?_, ?_, ?_⟩
  · intro s sc hsc q hq
    rw [hs] at hsc
    exact Heap.setCell_validAddr h a c (hv s sc hsc q hq)
  · intro s sc q hsc hq
    rw [hs] at hsc ⊢
    exact hp s sc q hsc hq
  · intro s sc q hsc hq
    rw [hs] at hsc
    exact hd s sc q hsc hq


/-! ## `Heap.newScope` -/

/-- `newScope` は、親が存在するなら有効（`p < scopes.size`）という仮定のもとで保存する。
    新しいスコープの添字は古い `scopes.size` なので、親は添字が小さい（`ParentsDecreasing`）。
    `vars` は空。 -/
theorem Heap.newScope_structWF (h : Heap) (parent : Option ScopeId) (hwf : h.StructWF)
    (hpar : ∀ p, parent = some p → p < h.scopes.size) : (h.newScope parent).1.StructWF := by
  obtain ⟨hv, hp, hd⟩ := hwf
  have hsc : (h.newScope parent).1.scopes = h.scopes.push { vars := [], parent } := rfl
  have hcl : (h.newScope parent).1.cells = h.cells := rfl
  have hva : ∀ q, (h.newScope parent).1.ValidAddr q ↔ h.ValidAddr q := by
    intro q; unfold Heap.ValidAddr; rw [hcl]
  have hsz : (h.newScope parent).1.scopes.size = h.scopes.size + 1 := by rw [hsc]; simp
  refine ⟨?_, ?_, ?_⟩
  · intro s sc hs q hq
    rw [hsc, Array.getElem?_push] at hs
    rw [hva]
    by_cases hse : s = h.scopes.size
    · rw [if_pos hse] at hs
      have := Option.some.inj hs; subst this; simp at hq
    · rw [if_neg hse] at hs
      exact hv s sc hs q hq
  · intro s sc q hs hq
    rw [hsc, Array.getElem?_push] at hs
    rw [hsz]
    by_cases hse : s = h.scopes.size
    · rw [if_pos hse] at hs
      have := Option.some.inj hs; subst this
      have hq' : parent = some q := hq
      exact Nat.lt_succ_of_lt (hpar q hq')
    · rw [if_neg hse] at hs
      exact Nat.lt_succ_of_lt (hp s sc q hs hq)
  · intro s sc q hs hq
    rw [hsc, Array.getElem?_push] at hs
    by_cases hse : s = h.scopes.size
    · rw [if_pos hse] at hs
      have := Option.some.inj hs; subst this
      have hq' : parent = some q := hq
      rw [hse]; exact hpar q hq'
    · rw [if_neg hse] at hs
      exact hd s sc q hs hq


/-! ## `Heap.bind` -/

/-- `bind` が作る `vars` の要素は、元の `vars` の要素か新しい束縛 `(n, a)`。 -/
private theorem mem_bind_vars (vars : List (String × Addr)) (n : String) (a : Addr) (p : String × Addr)
    (hp : p ∈ (if vars.any (·.1 == n) then vars.map (fun q => if q.1 == n then (n, a) else q)
               else vars ++ [(n, a)])) : p ∈ vars ∨ p = (n, a) := by
  split at hp
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    by_cases hqn : (q.1 == n) = true
    · right; simp [hqn]
    · left; simpa [hqn] using hq
  · rcases List.mem_append.mp hp with h | h
    · exact Or.inl h
    · right; simpa using h

/-- `bind` は、新しいアドレス `a` が有効であれば構造的整合性を保存する。
    束縛先のスコープが存在しなければ `bind` は何もしない（`h` のまま）ので、スコープの有効性の仮定は要らない。
    **`a` が有効でない場合は保存されない**（下の `bind_invalid_breaks_varsValid` に具体例）。 -/
theorem Heap.bind_structWF (h : Heap) (s : ScopeId) (n : String) (a : Addr) (hwf : h.StructWF)
    (ha : h.ValidAddr a) : (h.bind s n a).StructWF := by
  obtain ⟨hv, hp, hd⟩ := hwf
  unfold Heap.bind
  split
  · exact ⟨hv, hp, hd⟩
  · rename_i sc hsc
    have hs : s < h.scopes.size := by
      rcases Nat.lt_or_ge s h.scopes.size with hlt | hge
      · exact hlt
      · rw [Array.getElem?_eq_none hge] at hsc; cases hsc
    -- 新しい Scope 配列の添字アクセス
    have hget : ∀ s', (h.scopes.set! s { sc with vars := (if sc.vars.any (·.1 == n)
          then sc.vars.map (fun q => if q.1 == n then (n, a) else q) else sc.vars ++ [(n, a)]) })[s']? =
        if s = s' then some { sc with vars := (if sc.vars.any (·.1 == n)
          then sc.vars.map (fun q => if q.1 == n then (n, a) else q) else sc.vars ++ [(n, a)]) }
        else h.scopes[s']? := by
      intro s'
      simp [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hs]
    have hsize : (h.scopes.set! s { sc with vars := (if sc.vars.any (·.1 == n)
          then sc.vars.map (fun q => if q.1 == n then (n, a) else q) else sc.vars ++ [(n, a)]) }).size
        = h.scopes.size := by simp [Array.set!_eq_setIfInBounds]
    refine ⟨?_, ?_, ?_⟩
    · intro s' sc' hs' q hq
      simp only [hget] at hs'
      by_cases hse : s = s'
      · rw [if_pos hse] at hs'
        have := Option.some.inj hs'; subst this
        rcases mem_bind_vars sc.vars n a q hq with hq | rfl
        · have hsc' : h.scopes[s]? = some sc := hsc
          exact hv s sc hsc' q hq
        · exact ha
      · rw [if_neg hse] at hs'
        exact hv s' sc' hs' q hq
    · intro s' sc' q hs' hq
      simp only [hget] at hs'
      show q < (h.scopes.set! s _).size
      rw [hsize]
      by_cases hse : s = s'
      · rw [if_pos hse] at hs'
        have := Option.some.inj hs'; subst this
        exact hp s sc q hsc hq
      · rw [if_neg hse] at hs'
        exact hp s' sc' q hs' hq
    · intro s' sc' q hs' hq
      simp only [hget] at hs'
      by_cases hse : s = s'
      · rw [if_pos hse] at hs'
        have := Option.some.inj hs'; subst this
        rw [← hse]; exact hd s sc q hsc hq
      · rw [if_neg hse] at hs'
        exact hd s' sc' q hs' hq


/-! ## 反例 -/

/-- 無効なアドレスを `bind` すると `VarsValid` が壊れる（`bind_structWF` の仮定 `ha` が必要な理由）:
    初期 Heap のスコープ 1 に、存在しないアドレス 99 を束縛した例。 -/
theorem bind_invalid_breaks_varsValid : ¬ (Heap.initial.bind 1 "x" 99).VarsValid := by
  intro hv
  have hget : (Heap.initial.bind 1 "x" 99).scopes[1]? = some { vars := [("x", 99)], parent := some 0 } := rfl
  have hv' := hv 1 _ hget ("x", 99) (by simp)
  have hsz : (Heap.initial.bind 1 "x" 99).cells.size = 2 := rfl
  unfold Heap.ValidAddr at hv'
  rw [hsz] at hv'
  exact absurd hv' (by decide)

/-- 自己参照する親（スコープ 0 の親がスコープ 0）は `ParentsValid` を満たすが `ParentsDecreasing` を
    満たさない。`Heap.lookup` は fuel（`scopes.size + 1`）で打ち切るので停止はするが、
    循環が無いことの保証（`ParentsDecreasing`）は別に要る。 -/
theorem selfParent_valid_not_decreasing :
    let h : Heap := { cells := #[], scopes := #[{ vars := [], parent := some 0 }] }
    h.ParentsValid ∧ ¬ h.ParentsDecreasing := by
  intro h
  constructor
  · intro s sc q hs hq
    have hs' : s = 0 := by
      rcases s with _ | s
      · rfl
      · simp [h] at hs
    subst hs'
    simp [h] at hs; subst hs; simp at hq; subst hq; simp [h]
  · intro hd
    have := hd 0 { vars := [], parent := some 0 } 0 rfl rfl
    exact absurd this (by decide)

end Les.Eval
