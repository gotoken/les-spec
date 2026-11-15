import Les.Eval.Eval
import Les.Proofs.Heap
import Les.Proofs.Memo

/-
P2c-1/2: `Env.snap` に捕捉されたアドレスの保存性（E14）と、
捕捉時に未束縛だった名前の前方参照・再束縛（E15）。
対象は既存の `lookupEnv` / `capture` / `Heap.lookup` / `Heap.bind`（定義は変更しない）。
`sorry` / `admit` / 新たな公理は使わない。

捕捉済みの名前は `snap` のアドレスを使い続け、`Heap.bind` 自体はその Cell を変えない。
ただし後の `whnf` による `suspended → done` など、Cell の内容が永久に不変とは主張しない。
未捕捉の名前は生きたスコープから解決するが、参照するスコープの存在や束縛後の
アドレス有効性には、各定理に記載した条件が必要。
-/
namespace Les.Eval
open Les.Syntax

/-! ## 1. `lookupEnv` と `snap` -/

/-- `snap` を先頭から探して最初に見つかる `n` の組が `(k, a)` なら、`lookupEnv` は（Heap によらず）`a`。
    重複があれば先頭が優先される（`find?` の意味）。 -/
theorem lookupEnv_of_snap (heap : Heap) (env : Env) (n : String) (k : String) (a : Addr)
    (h : env.snap.find? (·.1 == n) = some (k, a)) : lookupEnv heap env n = some a := by
  unfold lookupEnv
  rw [h]

/-- `snap` に `n` が無ければ、`lookupEnv` は生きたスコープの `lookup`（E15）。 -/
theorem lookupEnv_of_not_snap (heap : Heap) (env : Env) (n : String)
    (h : env.snap.find? (·.1 == n) = none) : lookupEnv heap env n = heap.lookup env.scope n := by
  unfold lookupEnv
  rw [h]

/-- 1. 捕捉済みの名前は、同じ名前が生きたスコープで再束縛されても（`Heap.bind` を何度でも、
    どのスコープ・どのアドレスに対してでも）同じアドレスを返す。束縛先のスコープが存在しない場合
    （`bind` は何もしない）や、無効なアドレスを束縛する場合も含めて、条件は要らない。 -/
theorem lookupEnv_bind_of_snap (heap : Heap) (env : Env) (n : String) (k : String) (a : Addr)
    (h : env.snap.find? (·.1 == n) = some (k, a)) (s : ScopeId) (n' : String) (a' : Addr) :
    lookupEnv (heap.bind s n' a') env n = some a :=
  lookupEnv_of_snap _ env n k a h

/-- 複数回の再束縛（任意の `bind` の列）でも同じ。 -/
theorem lookupEnv_binds_of_snap (heap : Heap) (env : Env) (n : String) (k : String) (a : Addr)
    (h : env.snap.find? (·.1 == n) = some (k, a)) (bs : List (ScopeId × String × Addr)) :
    lookupEnv (bs.foldl (fun hp b => hp.bind b.1 b.2.1 b.2.2) heap) env n = some a :=
  lookupEnv_of_snap _ env n k a h

/-- `snap` が `pre ++ (n, a) :: post` で `pre` に `n` が無ければ、先頭の一致は `(n, a)`（重複と探索順序）。 -/
theorem find_snap_of_split (pre post : List (String × Addr)) (n : String) (a : Addr)
    (hpre : ∀ p ∈ pre, ¬ (p.1 == n) = true) :
    (pre ++ (n, a) :: post).find? (·.1 == n) = some (n, a) := by
  induction pre with
  | nil => simp
  | cons p ps ih =>
    have hp : ¬ (p.1 == n) = true := hpre p (by simp)
    have hps : ∀ q ∈ ps, ¬ (q.1 == n) = true := fun q hq => hpre q (by simp [hq])
    have hf : (p.1 == n) = false := by simpa using hp
    simp only [List.cons_append, List.find?_cons, hf]
    exact ih hps

/-! ## 2. `Heap.bind` は Cell を変えない（P2a の再利用） -/

/-- 2. 再束縛操作そのものでは、捕捉済みアドレス `a` の Cell は変わらない
    （`Heap.bind_cell?`。アドレスや束縛先スコープの有効性は要らない）。 -/
theorem bind_preserves_snap_cell (heap : Heap) (s : ScopeId) (n' : String) (a' a : Addr) :
    (heap.bind s n' a').cell? a = heap.cell? a :=
  Heap.bind_cell? heap s n' a' a

/-- 1 と 2 の合成: 捕捉済みの名前が指す Cell は、再束縛の前後で（`lookupEnv` 経由でも）同じ。 -/
theorem snap_cell_preserved_by_bind (heap : Heap) (env : Env) (n : String) (k : String) (a : Addr)
    (h : env.snap.find? (·.1 == n) = some (k, a)) (s : ScopeId) (n' : String) (a' : Addr) :
    (lookupEnv (heap.bind s n' a') env n).bind (heap.bind s n' a').cell? =
      (lookupEnv heap env n).bind heap.cell? := by
  rw [lookupEnv_bind_of_snap heap env n k a h s n' a', lookupEnv_of_snap heap env n k a h]
  simp only [Option.bind_some]
  exact Heap.bind_cell? heap s n' a' a

/-- 捕捉済みアドレスが有効なら、再束縛後も有効（`Heap.bind_validAddr`）。 -/
theorem snap_valid_preserved_by_bind (heap : Heap) (s : ScopeId) (n' : String) (a' a : Addr)
    (ha : heap.ValidAddr a) : (heap.bind s n' a').ValidAddr a :=
  Heap.bind_validAddr heap s n' a' ha

/-! ## 3. `capture` の実装 -/

/-- `eraseDupsBy.loop` の要素は入力のどちらかから来る。 -/
private theorem loop_mem_sub (as bs : List String) (x : String)
    (h : x ∈ List.eraseDupsBy.loop (fun a b => a == b) as bs) : x ∈ as ∨ x ∈ bs := by
  induction as generalizing bs with
  | nil => simp [List.eraseDupsBy.loop] at h; right; exact h
  | cons a as ih =>
    simp only [List.eraseDupsBy.loop] at h
    split at h
    · rcases ih bs h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h
    · rcases ih (a :: bs) h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · simp at h; rcases h with h | h
        · exact Or.inl (by simp [h])
        · exact Or.inr h

private theorem loop_mem_of (as bs : List String) (x : String)
    (h : x ∈ as ∨ x ∈ bs) : x ∈ List.eraseDupsBy.loop (fun a b => a == b) as bs := by
  induction as generalizing bs with
  | nil => simp [List.eraseDupsBy.loop]; rcases h with h | h <;> simp_all
  | cons a as ih =>
    simp only [List.eraseDupsBy.loop]
    split
    · rename_i hany
      apply ih
      rcases h with h | h
      · simp at h
        rcases h with hxa | h
        · right
          have hex : ∃ b ∈ bs, x = b := by simpa [List.any_eq_true, hxa] using hany
          obtain ⟨b, hb, hxb⟩ := hex
          rw [hxb]; exact hb
        · exact Or.inl h
      · exact Or.inr h
    · apply ih
      rcases h with h | h
      · simp at h
        rcases h with rfl | h
        · exact Or.inr (by simp)
        · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

/-- `eraseDups` は要素の集合を変えない（`capture` の名前リストの扱いに必要な範囲）。 -/
theorem mem_eraseDups_iff (ns : List String) (x : String) : x ∈ ns.eraseDups ↔ x ∈ ns := by
  unfold List.eraseDups List.eraseDupsBy
  constructor
  · intro h
    rcases loop_mem_sub ns [] x h with h | h
    · exact h
    · cases h
  · intro h; exact loop_mem_of ns [] x (Or.inl h)

/-- `capture` が `snap` に入れる組のリスト（実装の `let snap := …` と同じ式）。 -/
def captureSnap (heap : Heap) (env : Env) (e : Expr) : List (String × Addr) :=
  ((exprNames e).eraseDups).filterMap fun n => (lookupEnv heap env n).map (n, ·)

/-- `capture` の実行結果（実装そのもの）: 状態は変わらず、`snap` は `captureSnap`、`scope` は元のまま。 -/
theorem capture_run (e : Expr) (env : Env) (m : Machine) :
    ((capture e env).run).run m =
      (Except.ok { snap := captureSnap m.heap env e, scope := env.scope }, m) := rfl

/-- `captureSnap` で `find?` した結果: 名前リスト上で最初に「名前が `n` で、`lookupEnv` が解決できる」要素。 -/
theorem find_captureSnap (heap : Heap) (env : Env) (e : Expr) (n : String) (a : Addr)
    (hn : n ∈ exprNames e) (ha : lookupEnv heap env n = some a) :
    (captureSnap heap env e).find? (·.1 == n) = some (n, a) := by
  unfold captureSnap
  rw [List.find?_filterMap]
  have hmem := (mem_eraseDups_iff (exprNames e) n).mpr hn
  -- 述語を満たす最初の名前 k は n（`lookupEnv` を引いた組のキーは k 自身）
  have key : ∀ (ns : List String), n ∈ ns →
      (List.find? (fun k => Option.any (fun p : String × Addr => p.1 == n)
        ((lookupEnv heap env k).map (k, ·))) ns).bind
        (fun k => (lookupEnv heap env k).map (k, ·)) = some (n, a) := by
    intro ns
    induction ns with
    | nil => intro h; cases h
    | cons k ks ih =>
      intro hk
      by_cases hkn : k = n
      · subst hkn
        simp [ha]
      · have hk' : n ∈ ks := by
          rcases List.mem_cons.mp hk with h | h
          · exact absurd h.symm hkn
          · exact h
        have hfalse : Option.any (fun p : String × Addr => p.1 == n)
            ((lookupEnv heap env k).map (k, ·)) = false := by
          cases hl : lookupEnv heap env k <;> simp [hkn]
        simp only [List.find?_cons, hfalse]
        exact ih hk'
  exact key _ hmem

/-- 3. 実装に対する保存性: 作成時点で `lookupEnv` が解決できる、式に現れる名前 `n` は、
    捕捉された環境の `snap` に入り、以降は**どの Heap でも・どの再束縛の後でも**同じアドレス `a` を返す。 -/
theorem capture_preserves (e : Expr) (env : Env) (m m' : Machine) (env' : Env) (n : String) (a : Addr)
    (hn : n ∈ exprNames e) (ha : lookupEnv m.heap env n = some a)
    (hrun : ((capture e env).run).run m = (Except.ok env', m')) (heap' : Heap) :
    lookupEnv heap' env' n = some a := by
  rw [capture_run] at hrun
  have h1 : env' = { snap := captureSnap m.heap env e, scope := env.scope } :=
    (Except.ok.inj (Prod.mk.inj hrun).1).symm
  subst h1
  exact lookupEnv_of_snap heap' _ n n a (find_captureSnap m.heap env e n a hn ha)

/-- 3'. 上に再束縛を重ねた形: 捕捉後に生きたスコープで `n` が（あるいは他の名前が）再束縛されても、
    `lookupEnv` は `a` を返し、`a` の Cell は変わらない。 -/
theorem capture_preserves_under_bind (e : Expr) (env : Env) (m m' : Machine) (env' : Env) (n : String)
    (a : Addr) (hn : n ∈ exprNames e) (ha : lookupEnv m.heap env n = some a)
    (hrun : ((capture e env).run).run m = (Except.ok env', m'))
    (heap' : Heap) (s : ScopeId) (n' : String) (a' : Addr) :
    lookupEnv (heap'.bind s n' a') env' n = some a ∧
      (heap'.bind s n' a').cell? a = heap'.cell? a :=
  ⟨capture_preserves e env m m' env' n a hn ha hrun _, Heap.bind_cell? heap' s n' a' a⟩

/-- 捕捉されなかった名前（作成時に未束縛）は `snap` に入らず、生きたスコープを引く（E15）。
    こちらは保存性の対象外で、再束縛の影響を受ける。 -/
theorem capture_unbound (e : Expr) (env : Env) (n : String) (heap : Heap)
    (hu : lookupEnv heap env n = none) :
    (captureSnap heap env e).find? (·.1 == n) = none := by
  unfold captureSnap
  rw [List.find?_eq_none]
  intro p hp
  rw [List.mem_filterMap] at hp
  obtain ⟨k, _, hk⟩ := hp
  cases hl : lookupEnv heap env k with
  | none => simp [hl] at hk
  | some b =>
    simp [hl] at hk
    subst hk
    intro hkn
    have hkn' : k = n := by simpa using hkn
    subst hkn'
    rw [hu] at hl
    cases hl


/-! ## P2c-2: 捕捉されなかった名前の前方参照と再束縛（E15）

対象は `lookupEnv` までの参照解決。`whnf` が値を返すまでの正しさ、親スコープの循環や不正な
参照を含む Heap 全体の整合性は仮定も証明もしない。
「名前が束縛で解決できる」ことと「そのアドレスが有効な Cell を指す」ことは区別する:
前者は `lookupEnv = some a`、後者は別途 `heap.ValidAddr a`。 -/

/-- 親をたどる探索で、ローカルに束縛があればそれが優先される（親の同名束縛は見えない）。 -/
theorem Heap.lookup_of_lookupLocal (h : Heap) (s : ScopeId) (n : String) (a : Addr)
    (hl : h.lookupLocal s n = some a) : h.lookup s n = some a := by
  unfold Heap.lookup
  unfold Heap.lookupFrom
  rw [hl]

/-- 4. ローカルの束縛は、親スコープの同名の束縛より優先される。 -/
theorem Heap.lookup_local_priority (h : Heap) (s p : ScopeId) (n : String) (a a' : Addr)
    (hl : h.lookupLocal s n = some a) (_hp : h.lookup p n = some a') : h.lookup s n = some a :=
  Heap.lookup_of_lookupLocal h s n a hl

/-- `bind` 直後、束縛先のスコープ（存在する）からの `lookup` はその束縛を返す。 -/
theorem Heap.lookup_bind_self (h : Heap) (s : ScopeId) (n : String) (a : Addr)
    (hs : s < h.scopes.size) : (h.bind s n a).lookup s n = some a :=
  Heap.lookup_of_lookupLocal _ s n a (Heap.bind_lookupLocal_self h s n a hs)

/-- 再束縛（同じスコープで同じ名前をさらに束縛）すると、最新の束縛が見える。 -/
theorem Heap.lookup_rebind (h : Heap) (s : ScopeId) (n : String) (a b : Addr)
    (hs : s < h.scopes.size) : ((h.bind s n a).bind s n b).lookup s n = some b := by
  apply Heap.lookup_bind_self
  rw [Heap.bind_scopes_size]; exact hs

/-- 1. `capture` 実行時に未束縛だった名前は、生成された `snap` に入らず、`lookupEnv` は
    生きたスコープ（`env.scope`）の `lookup` に解決される。名前が式に現れるかどうかは問わない。
    `snap` に無いことは P2c-1 の `capture_unbound` から導く。 -/
theorem capture_unbound_lookup (e : Expr) (env : Env) (m m' : Machine) (env' : Env) (n : String)
    (hunb : lookupEnv m.heap env n = none)
    (hrun : ((capture e env).run).run m = (Except.ok env', m')) (heap' : Heap) :
    env'.snap.find? (·.1 == n) = none ∧ env'.scope = env.scope ∧
      lookupEnv heap' env' n = heap'.lookup env.scope n := by
  rw [capture_run] at hrun
  have h1 : env' = { snap := captureSnap m.heap env e, scope := env.scope } :=
    (Except.ok.inj (Prod.mk.inj hrun).1).symm
  subst h1
  have hnone := capture_unbound e env n m.heap hunb
  exact ⟨hnone, rfl, lookupEnv_of_not_snap heap' _ n hnone⟩

/-- 2. 前方参照: 生成された環境の生きたスコープ（存在する）に後から `n` を `a` で束縛すると、
    `lookupEnv` は `some a`。束縛先のスコープが `env'.scope` であることが前提。 -/
theorem forward_ref_resolves (e : Expr) (env : Env) (m m' : Machine) (env' : Env) (n : String)
    (a : Addr) (hunb : lookupEnv m.heap env n = none)
    (hrun : ((capture e env).run).run m = (Except.ok env', m'))
    (heap' : Heap) (hs : env.scope < heap'.scopes.size) :
    lookupEnv (heap'.bind env.scope n a) env' n = some a := by
  obtain ⟨hnone, hscope, _⟩ := capture_unbound_lookup e env m m' env' n hunb hrun (heap'.bind env.scope n a)
  rw [lookupEnv_of_not_snap _ env' n hnone, hscope]
  exact Heap.lookup_bind_self heap' env.scope n a hs

/-- 3. 後からさらに再束縛しても、最新の束縛（`b`）が見える。 -/
theorem forward_ref_rebound (e : Expr) (env : Env) (m m' : Machine) (env' : Env) (n : String)
    (a b : Addr) (hunb : lookupEnv m.heap env n = none)
    (hrun : ((capture e env).run).run m = (Except.ok env', m'))
    (heap' : Heap) (hs : env.scope < heap'.scopes.size) :
    lookupEnv ((heap'.bind env.scope n a).bind env.scope n b) env' n = some b := by
  obtain ⟨hnone, hscope, _⟩ :=
    capture_unbound_lookup e env m m' env' n hunb hrun ((heap'.bind env.scope n a).bind env.scope n b)
  rw [lookupEnv_of_not_snap _ env' n hnone, hscope]
  exact Heap.lookup_rebind heap' env.scope n a b hs

/-- 解決できること（アドレスが返る）と、そのアドレスが有効な Cell を指すことは別。
    束縛するアドレス `a` が有効なら、`bind` の後も有効で、Cell も `bind` では変わらない。 -/
theorem forward_ref_cell (heap' : Heap) (s : ScopeId) (n : String) (a : Addr)
    (ha : heap'.ValidAddr a) :
    (heap'.bind s n a).ValidAddr a ∧ (heap'.bind s n a).cell? a = heap'.cell? a :=
  ⟨Heap.bind_validAddr heap' s n a ha, Heap.bind_cell? heap' s n a a⟩

end Les.Eval
