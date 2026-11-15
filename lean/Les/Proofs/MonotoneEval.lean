import Les.Eval.Eval
import Les.Proofs.Monotone

/-
P2d-3: 評価器の Cell 数単調性。実際の `Les/Eval/Eval.lean` の `evalE` / `whnf` / `demand` / … について、
`Mono`（P2d-2 の定義、変更なし）が任意の fuel・引数で成り立つことを、fuel に関する帰納法で示す。
これらは fuel を減らして呼び合うので、循環した仮定は置かない: fuel `n + 1` の各関数の証明は、fuel `n` の全関数の
単調性（帰納法の仮定）だけを使う。`sorry` / `admit` / 新たな公理は使わない。
-/
namespace Les.Eval
open Les.Syntax

/-! ## 1. 再帰的評価を伴わない補助関数 -/

theorem mono_primErr {α : Type} (msg : String) : Mono (primErr msg : EvalM α) := mono_throw _

theorem mono_capture (e : Expr) (env : Env) : Mono (capture e env) :=
  mono_bind mono_getHeap fun _ => mono_pure _

theorem mono_arith (op : String) (a b : Value) : Mono (arith op a b) := by
  unfold arith
  repeat' (first | split | exact mono_pure _ | exact mono_throw _ | exact mono_primErr _)

theorem mono_showValue (v : Value) : Mono (showValue v) := by
  unfold showValue
  repeat' (first | split | exact mono_pure _ | exact mono_throw _)

-- 単調性の証明用: `Mono` の目標を `mono_bind` などで分解し、葉は既知の補題か帰納法の仮定
-- （`ihE` など。使う側のスコープで解決する）で閉じる。
set_option hygiene false in
macro "mono_tac" : tactic => `(tactic| repeat' (first
  | split
  | with_reducible exact mono_pure _ | with_reducible exact mono_throw _ | with_reducible exact mono_getHeap | with_reducible exact mono_alloc _
  | with_reducible exact mono_primErr _ | with_reducible exact mono_capture _ _ | with_reducible exact mono_arith _ _ _ | with_reducible exact mono_showValue _
  | with_reducible exact mono_modHeap_bind _ _ _ | with_reducible exact mono_modHeap_setCell _ _ | with_reducible exact mono_modify_stdout _
  | with_reducible exact mono_newScope _ | with_reducible exact mono_bindParams _ _ _
  | with_reducible exact ihE _ _ | with_reducible exact ihW _ | with_reducible exact ihD _ _ | with_reducible exact ihB _ _ | with_reducible exact ihC _ _ _ _ | with_reducible exact ihAs _ _
  | with_reducible exact ihA _ _ | with_reducible exact ihF _ | with_reducible exact ihBl _ _ | with_reducible exact ihX _ _ | with_reducible exact ihXc _ _
  | apply mono_bind | apply mono_tryCatch | apply mono_mapM | apply mono_foldlM
  | intro _))

/-! ## 2. 繰り返し（`foldlM` / `mapM` / `forM` / 仮引数の束縛） -/

theorem mono_foldlM {α β : Type} (f : β → α → EvalM β) (hf : ∀ b a, Mono (f b a)) :
    ∀ (l : List α) (b : β), Mono (l.foldlM f b)
  | [], b => by rw [List.foldlM_nil]; exact mono_pure _
  | a :: l, b => by
    rw [List.foldlM_cons]
    exact mono_bind (hf b a) fun b' => mono_foldlM f hf l b'

theorem mono_mapM {α β : Type} (f : α → EvalM β) (hf : ∀ a, Mono (f a)) :
    ∀ l : List α, Mono (l.mapM f)
  | [] => by rw [List.mapM_nil]; exact mono_pure _
  | a :: l => by
    rw [List.mapM_cons]
    exact mono_bind (hf a) fun _ => mono_bind (mono_mapM f hf l) fun _ => mono_pure _

theorem mono_forM {α : Type} (f : α → EvalM Unit) (hf : ∀ a, Mono (f a)) :
    ∀ l : List α, Mono (forM l f)
  | [] => by rw [List.forM_nil]; exact mono_pure _
  | a :: l => by
    rw [List.forM_cons]
    exact mono_bind (hf a) fun _ => mono_forM f hf l

/-- `callClosure` の局所再帰（仮引数の束縛）。fuel を使わず、仮引数のリストの長さで再帰する。 -/
theorem mono_bindParams (sc : ScopeId) :
    ∀ (ps : List Param) (cs : List Addr), Mono (callClosure.bindParams sc ps cs)
  | [], cs => by unfold callClosure.bindParams; exact mono_pure _
  | p :: ps, cs => by
    unfold callClosure.bindParams
    cases cs <;> (dsimp only; mono_tac)

/-! ## 3. 相互再帰の関数群（fuel に関する帰納法） -/

/-- fuel `n` での全関数の単調性。 -/
def MonoAt (n : Nat) : Prop :=
  (∀ e env, Mono (evalE n e env)) ∧
  (∀ a, Mono (whnf n a)) ∧
  (∀ e env, Mono (demand n e env)) ∧
  (∀ b cells, Mono (callBuiltin n b cells)) ∧
  (∀ ps body cs cells, Mono (callClosure n ps body cs cells)) ∧
  (∀ args env, Mono (prepArgs n args env)) ∧
  (∀ a env, Mono (prepArg n a env)) ∧
  (∀ cells, Mono (forceAll n cells)) ∧
  (∀ ss sc, Mono (execBlock n ss sc)) ∧
  (∀ s sc, Mono (exec n s sc)) ∧
  (∀ s sc, Mono (execCore n s sc))

theorem monoAt_zero : MonoAt 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e env; rw [evalE]; exact mono_throw _
  · intro a; rw [whnf]; exact mono_throw _
  · intro e env; rw [demand]; exact mono_throw _
  · intro b cells; rw [callBuiltin]; exact mono_throw _
  · intro ps body cs cells; rw [callClosure]; exact mono_throw _
  · intro args env; rw [prepArgs]; exact mono_throw _
  · intro a env; rw [prepArg]; exact mono_throw _
  · intro cells; rw [forceAll]; exact mono_throw _
  · intro ss sc; rw [execBlock]; exact mono_throw _
  · intro s sc; rw [exec]; exact mono_throw _
  · intro s sc; rw [execCore]; exact mono_throw _

set_option maxHeartbeats 2000000 in
theorem monoAt_succ (n : Nat) (ih : MonoAt n) : MonoAt (n + 1) := by
  obtain ⟨ihE, ihW, ihD, ihB, ihC, ihAs, ihA, ihF, ihBl, ihX, ihXc⟩ := ih
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e env; unfold evalE; mono_tac
  · intro a; unfold whnf; mono_tac
  · intro e env; unfold demand; mono_tac
  · intro b cells; unfold callBuiltin; cases b <;> (try dsimp only) <;> mono_tac
  · intro ps body cs cells; unfold callClosure; mono_tac
  · intro args env; unfold prepArgs; cases args <;> (try dsimp only) <;> mono_tac
  · intro a env; unfold prepArg; cases a <;> (try dsimp only) <;> mono_tac
  · intro cells; unfold forceAll; cases cells <;> (try dsimp only) <;> mono_tac
  · intro ss sc; unfold execBlock; mono_tac
  · intro s sc; unfold exec; mono_tac
  · intro s sc; unfold execCore; cases s <;> (try dsimp only) <;> mono_tac

theorem monoAt (n : Nat) : MonoAt n := by
  induction n with
  | zero => exact monoAt_zero
  | succ n ih => exact monoAt_succ n ih

/-- 最終目標: `demand` は任意の fuel・式・環境・Machine で Cell 数を減らさない
    （正常終了・`error`・`exit`・`unsupported`・`outOfFuel` のすべてを含む）。 -/
theorem demand_mono (fuel : Nat) (e : Expr) (env : Env) : Mono (demand fuel e env) :=
  (monoAt fuel).2.2.1 e env

theorem evalE_mono (fuel : Nat) (e : Expr) (env : Env) : Mono (evalE fuel e env) :=
  (monoAt fuel).1 e env

theorem whnf_mono (fuel : Nat) (a : Addr) : Mono (whnf fuel a) := (monoAt fuel).2.1 a

theorem execBlock_mono (fuel : Nat) (ss : List Stmt) (sc : ScopeId) : Mono (execBlock fuel ss sc) :=
  (monoAt fuel).2.2.2.2.2.2.2.2.1 ss sc

theorem exec_mono (fuel : Nat) (s : Stmt) (sc : ScopeId) : Mono (exec fuel s sc) :=
  (monoAt fuel).2.2.2.2.2.2.2.2.2.1 s sc

/-- 帰結: `demand` の開始時に有効なアドレスは、終了時（正常でも例外でも）にも有効。
    P2b-2 の `whnf_suspended_ok_cell` が仮定する有効性を導くための部品（この PR ではまだ取り除かない）。 -/
theorem demand_validAddr (fuel : Nat) (e : Expr) (env : Env) (m : Machine) {a : Addr}
    (ha : m.heap.ValidAddr a) : (((demand fuel e env).run).run m).2.heap.ValidAddr a :=
  mono_validAddr (demand_mono fuel e env) m ha

end Les.Eval
