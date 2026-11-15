import Les.Eval.Eval
import Les.Proofs.Heap
import Les.Proofs.Memo

/-
P2c-1: スナップショット（`Env.snap`）に捕捉されたアドレスの保存性。
対象は既存の `lookupEnv` / `capture` / `Heap.bind`（定義は変更しない）。
`sorry` / `admit` / 新たな公理は使わない。

主張するのは「`snap` に捕捉された名前は、どの Heap・どの再束縛の後でも同じアドレスを指し、
そのアドレスの Cell は再束縛操作そのものでは変わらない」ことだけ。Cell の値が永久に不変とは
言わない（後から `whnf` で強制すれば `suspended → done` に変わりうる）。捕捉されなかった名前は
生きたスコープを引く（E15）ので、この保存性の対象外。
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

end Les.Eval
