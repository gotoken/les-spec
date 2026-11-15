import Les.Eval.Eval
import Les.Proofs.Heap
import Les.Proofs.MonotoneEval

/-
P2b-1/2 の `whnf` の基本性質から、P2d-4 のアドレス有効性の導出、
P2d-5 の初回強制・メモ化・再強制の統合定理までを収める。
対象は `Les/Eval/Eval.lean` の実際の `whnf` であり、証明用の別実装ではない。
P2b-2 当時は一部で `hvalid` を仮定していたが、P2d-3/4 でその仮定を導出した。
最終的な `whnf_suspended_ok_memo` は `hvalid` と `hrun` を外部仮定にしない。
ただし `demand` の成功自体は `hd` で仮定しており、失敗後のメモ化は対象外。
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


/-! ## P2b-2: 未評価 Cell の初回強制とブラックホール

この節の元の定理は、`demand` の結果と必要に応じて最終状態でのアドレス有効性を
明示的な仮定として扱う。後の P2d-3/4 で `demand_validAddr` が証明され、
有効性を外部から仮定しない強化版を同じファイルの末尾に追加した。
Heap 全体の整合性保存や `demand` の成功は主張しない。 -/

/-- Cell が `some` ならアドレスは有効。 -/
theorem Heap.valid_of_cell?_some {h : Heap} {a : Addr} {c : Cell} (hc : h.cell? a = some c) :
    h.ValidAddr a := by
  unfold Heap.cell? at hc
  unfold Heap.ValidAddr
  by_cases hlt : a < h.cells.size
  · exact hlt
  · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hc
    cases hc

/-- 範囲外のアドレスの Cell は `none`。 -/
theorem Heap.cell?_none_of_not_valid {h : Heap} {a : Addr} (ha : ¬ h.ValidAddr a) :
    h.cell? a = none := by
  unfold Heap.cell?
  exact Array.getElem?_eq_none (Nat.le_of_not_lt ha)

/-- `modHeap f` は Heap だけを `f` で書き換え、値は `()`。 -/
theorem modHeap_run (f : Heap → Heap) (m : Machine) :
    ((modHeap f).run).run m = (Except.ok (), { m with heap := f m.heap }) := rfl

/-- 1. `blackhole` Cell を正の fuel で強制すると、位置なしの blackhole エラーで、Machine は変化しない。 -/
theorem whnf_blackhole (n : Nat) (a : Addr) (e : Expr) (m : Machine)
    (h : m.heap.cell? a = some (.blackhole e)) :
    ((whnf (n + 1) a).run).run m =
      (Except.error (Halt.error "blackhole: circular reference detected in lazy thunk" ErrPos.absent), m) := by
  rw [whnf, getHeap_bind]
  simp [h]
  rfl

/-- 2. 範囲外（Cell が `none`）のアドレスを正の fuel で強制すると、dangling-address エラーで、
    Machine は変化しない。 -/
theorem whnf_dangling (n : Nat) (a : Addr) (m : Machine) (h : m.heap.cell? a = none) :
    ((whnf (n + 1) a).run).run m =
      (Except.error (Halt.error "internal: dangling address" ErrPos.absent), m) := by
  rw [whnf, getHeap_bind]
  simp [h]
  rfl

theorem whnf_out_of_range (n : Nat) (a : Addr) (m : Machine) (h : ¬ m.heap.ValidAddr a) :
    ((whnf (n + 1) a).run).run m =
      (Except.error (Halt.error "internal: dangling address" ErrPos.absent), m) :=
  whnf_dangling n a m (Heap.cell?_none_of_not_valid h)

/-- 初回強制の入口で Cell を `blackhole` に書き換えた直後の Machine。 -/
def Machine.blackholed (m : Machine) (a : Addr) (e : Expr) : Machine :=
  { m with heap := m.heap.setCell a (.blackhole e) }

/-- 3. `suspended e env` の初回強制は、まず対象 Cell を `blackhole` にしてから `demand` を実行し、
    その結果を `done` として書き戻す（既存の `whnf` の展開そのもの）。書き込み前の状態は
    `m.blackholed a e` で、`demand n e env` はこの状態から走る。 -/
theorem whnf_suspended (n : Nat) (a : Addr) (e : Expr) (env : Env) (m : Machine)
    (h : m.heap.cell? a = some (.suspended e env)) :
    ((whnf (n + 1) a).run).run m =
      ((do let v ← demand n e env
           modHeap fun x => x.setCell a (.done v)
           pure v : EvalM Value).run).run
        (m.blackholed a e) := by
  rw [whnf, getHeap_bind]
  simp only [h]
  rw [run_bind_ok _ _ m (m.blackholed a e) () (modHeap_run _ m)]

/-- `blackholed` の直後、対象 Cell は `blackhole e`（再入すると `whnf_blackhole` に当たる）。 -/
theorem Machine.blackholed_cell? (m : Machine) (a : Addr) (e : Expr) {env : Env}
    (h : m.heap.cell? a = some (.suspended e env)) :
    (m.blackholed a e).heap.cell? a = some (.blackhole e) :=
  Heap.setCell_cell?_self m.heap _ (Heap.valid_of_cell?_some h)

/-- 3'. `demand` の実行中に同じアドレスを再び強制すると（`demand` がまだ Cell を書き換えていない状態では）
    blackhole エラーになる。`whnf_blackhole` と `blackholed_cell?` の合成。 -/
theorem whnf_reenter_blackholed (k : Nat) (a : Addr) (e : Expr) (env : Env) (m : Machine)
    (h : m.heap.cell? a = some (.suspended e env)) :
    ((whnf (k + 1) a).run).run (m.blackholed a e) =
      (Except.error (Halt.error "blackhole: circular reference detected in lazy thunk" ErrPos.absent),
        m.blackholed a e) :=
  whnf_blackhole k a e _ (m.blackholed_cell? a e h)

/-- 4. `demand` が `ok v` で終わる（最終状態 `m₂`）なら、`whnf` は `v` を返し、最終状態は
    `m₂` の Heap の対象アドレスに `done v` を書いたもの。範囲外への `set!` は何もしないので、
    この等式自体にアドレスの有効性は要らない。 -/
theorem whnf_suspended_ok (n : Nat) (a : Addr) (e : Expr) (env : Env) (m m₂ : Machine) (v : Value)
    (h : m.heap.cell? a = some (.suspended e env))
    (hd : ((demand n e env).run).run (m.blackholed a e) = (Except.ok v, m₂)) :
    ((whnf (n + 1) a).run).run m =
      (Except.ok v, { m₂ with heap := m₂.heap.setCell a (.done v) }) := by
  rw [whnf_suspended n a e env m h, run_bind_ok _ _ _ m₂ v hd]
  rfl

/-- 4'. 成功した初回強制の後、対象アドレスの Cell は `done v`。書き込みが実際に起きる条件として、
    `demand` 終了後の状態 `m₂` でアドレスが有効であること（`hvalid`）を**仮定**する
    （P2b-2 当時の条件付き補題。P2d-4 の `whnf_suspended_ok_cell_valid` は、
    `demand_validAddr` を使ってこの `hvalid` を導出する）。 -/
theorem whnf_suspended_ok_cell (n : Nat) (a : Addr) (e : Expr) (env : Env) (m m₂ m₃ : Machine)
    (v : Value) (h : m.heap.cell? a = some (.suspended e env))
    (hd : ((demand n e env).run).run (m.blackholed a e) = (Except.ok v, m₂))
    (hvalid : m₂.heap.ValidAddr a)
    (hrun : ((whnf (n + 1) a).run).run m = (Except.ok v, m₃)) :
    m₃.heap.cell? a = some (.done v) := by
  rw [whnf_suspended_ok n a e env m m₂ v h hd] at hrun
  have hm : m₃ = { m₂ with heap := m₂.heap.setCell a (.done v) } := (Prod.mk.inj hrun).2.symm
  subst hm
  exact Heap.setCell_cell?_self m₂.heap _ hvalid

/-- 5. P2b-1 への接続: 成功した初回強制の後、同じ Cell を再び強制しても値は `v` のままで、
    Machine は変化しない。 -/
theorem whnf_suspended_ok_then_stable (n k : Nat) (a : Addr) (e : Expr) (env : Env)
    (m m₂ m₃ : Machine) (v : Value) (h : m.heap.cell? a = some (.suspended e env))
    (hd : ((demand n e env).run).run (m.blackholed a e) = (Except.ok v, m₂))
    (hvalid : m₂.heap.ValidAddr a)
    (hrun : ((whnf (n + 1) a).run).run m = (Except.ok v, m₃)) :
    ((whnf (k + 1) a).run).run m₃ = (Except.ok v, m₃) :=
  whnf_done k a v m₃ (whnf_suspended_ok_cell n a e env m m₂ m₃ v h hd hvalid hrun)

/-! ## P2d-4: `hvalid` の導出（P2d-3 の `demand_validAddr` から）

`demand` 終了後のアドレスの有効性は、`demand` の Cell 数単調性（P2d-3）から出る。
`demand` が正常終了すること自体は保証しない（`hd` が残る仮定）。 -/

/-- 1. `suspended` な Cell のアドレスは、`blackholed` 後の Machine でも有効（`setCell` は Cell 数を変えない）。 -/
theorem Machine.blackholed_validAddr (m : Machine) (a : Addr) (e : Expr) {env : Env}
    (h : m.heap.cell? a = some (.suspended e env)) :
    (m.blackholed a e).heap.ValidAddr a :=
  Heap.setCell_validAddr m.heap a (.blackhole e) (Heap.valid_of_cell?_some h)

/-- 2. `demand` が `m.blackholed a e` から `m₂` で終了したなら（正常終了でも例外でも）`m₂` で `a` は有効。
    `hd` は結果の形を問わず、最終状態が `m₂` であることだけを使う。 -/
theorem demand_blackholed_validAddr (n : Nat) (a : Addr) (e : Expr) (env : Env) (m m₂ : Machine)
    {r : Except Halt Value} (h : m.heap.cell? a = some (.suspended e env))
    (hd : ((demand n e env).run).run (m.blackholed a e) = (r, m₂)) :
    m₂.heap.ValidAddr a := by
  have := demand_validAddr n e env (m.blackholed a e) (m.blackholed_validAddr a e h)
  rw [hd] at this
  exact this

/-- 3. `hvalid` なしの `whnf_suspended_ok_cell`。残る仮定は初期 Cell が `suspended` であることと、
    `demand` が `ok v` で終了したこと（`hd`）、および `whnf` の実行結果（`hrun`）だけ。 -/
theorem whnf_suspended_ok_cell_valid (n : Nat) (a : Addr) (e : Expr) (env : Env) (m m₂ m₃ : Machine)
    (v : Value) (h : m.heap.cell? a = some (.suspended e env))
    (hd : ((demand n e env).run).run (m.blackholed a e) = (Except.ok v, m₂))
    (hrun : ((whnf (n + 1) a).run).run m = (Except.ok v, m₃)) :
    m₃.heap.cell? a = some (.done v) :=
  whnf_suspended_ok_cell n a e env m m₂ m₃ v h hd
    (demand_blackholed_validAddr n a e env m m₂ h hd) hrun

/-- 4. `hvalid` なしの `whnf_suspended_ok_then_stable`。 -/
theorem whnf_suspended_ok_then_stable_valid (n k : Nat) (a : Addr) (e : Expr) (env : Env)
    (m m₂ m₃ : Machine) (v : Value) (h : m.heap.cell? a = some (.suspended e env))
    (hd : ((demand n e env).run).run (m.blackholed a e) = (Except.ok v, m₂))
    (hrun : ((whnf (n + 1) a).run).run m = (Except.ok v, m₃)) :
    ((whnf (k + 1) a).run).run m₃ = (Except.ok v, m₃) :=
  whnf_suspended_ok_then_stable n k a e env m m₂ m₃ v h hd
    (demand_blackholed_validAddr n a e env m m₂ h hd) hrun

/-! ## P2d-5: 成功した初回強制とメモ化の統合定理 -/

/-- 統合定理。初期状態で `a` が `suspended e env` を指し、`m.blackholed a e` から走らせた
    `demand n e env` が `ok v`（最終状態 `m₂`）で終わるなら、次がすべて成り立つ:
    1. `whnf (n+1) a` は `ok v` を返し、最終状態は `m₃ = m₂` の対象アドレスに `done v` を書いたもの。
    2. `m₃` で対象アドレスの Cell は `done v`。
    3. 任意の fuel `k + 1` で `m₃` からもう一度 `whnf` すると `ok v` を返し、Machine は変化しない。
    仮定は `h`（初期 Cell が `suspended`）と `hd`（`demand` が `ok v` で終了）だけ。
    `demand` の成功は保証せず、失敗後のメモ化は扱わない。 -/
theorem whnf_suspended_ok_memo (n : Nat) (a : Addr) (e : Expr) (env : Env) (m m₂ : Machine)
    (v : Value) (h : m.heap.cell? a = some (.suspended e env))
    (hd : ((demand n e env).run).run (m.blackholed a e) = (Except.ok v, m₂)) :
    ((whnf (n + 1) a).run).run m =
        (Except.ok v, { m₂ with heap := m₂.heap.setCell a (.done v) }) ∧
      ({ m₂ with heap := m₂.heap.setCell a (.done v) }).heap.cell? a = some (.done v) ∧
      ∀ k, ((whnf (k + 1) a).run).run { m₂ with heap := m₂.heap.setCell a (.done v) } =
        (Except.ok v, { m₂ with heap := m₂.heap.setCell a (.done v) }) := by
  have h1 := whnf_suspended_ok n a e env m m₂ v h hd
  have h2 := whnf_suspended_ok_cell_valid n a e env m m₂ _ v h hd h1
  exact ⟨h1, h2, fun k => whnf_done k a v _ h2⟩

end Les.Eval
