import Les.Proofs.Memo
import Les.Proofs.WellFormed

/-!
# P2d-5: `whnf_suspended_ok_memo` の非空虚性

実際の `Heap.initial` から未評価の整数リテラル Cell を 1 つ割り当てる。
`suspended` という前提と、`blackholed` 後の `demand` が成功するという前提を
**同じ具体例**で満たし、統合定理の結論を導く。

別の意味論・評価器は作らない。既存の `demand` / `whnf` / `Heap` を使用する。
これは Lean モデルでの非空虚性であり、Go 実装との同値性は示さない。
-/

namespace Les.Eval
open Les.Syntax

/-- 位置 1:1 の整数リテラル。`demand 2` が正常終了する最小の式。 -/
def memoWitnessExpr : Expr := .int { line := 1, col := 1 } 42

/-- Go 側の型解析済みプログラムのグローバルスコープに対応する環境。 -/
def memoWitnessEnv : Env := { snap := [], scope := globalScope }

def memoWitnessCell : Cell := .suspended memoWitnessExpr memoWitnessEnv

/-- 空の任意 Heap でなく、評価器が利用する `Heap.initial` からの割当。 -/
def memoWitnessMachine : Machine :=
  { heap := (Heap.initial.alloc memoWitnessCell).1, stdout := "" }

def memoWitnessAddr : Addr := (Heap.initial.alloc memoWitnessCell).2

/-- 整数リテラルの `demand 2` は `done` Cell を割り当て、その値を返す。
    `rfl` で状態全体を計算する代わりに、割当直後の Cell と `whnf_done`
    から成功を示す。具体例だけでなく任意の初期 Machine に対して成立する。 -/
private theorem demand_int_ok (m : Machine) (p : Pos) (i : Int) (env : Env) :
    ((demand 2 (.int p i) env).run).run m =
      (Except.ok (.int i), { m with heap := (m.heap.alloc (.done (.int i))).1 }) := by
  let a : Addr := (m.heap.alloc (.done (.int i))).2
  let m' : Machine := { m with heap := (m.heap.alloc (.done (.int i))).1 }
  have heval :
      ((evalE 1 (.int p i) env).run).run m = (Except.ok a, m') := by
    rw [evalE]
    rfl
  have hcell : m'.heap.cell? a = some (.done (.int i)) := by
    simpa only [m', a] using Heap.alloc_cell?_new m.heap (.done (.int i))
  have hwhnf : ((whnf 1 a).run).run m' = (Except.ok (.int i), m') :=
    whnf_done 0 a (.int i) m' hcell
  have hbody :
      (((evalE 1 (.int p i) env >>= fun b => whnf 1 b).run).run m) =
        (Except.ok (.int i), m') := by
    rw [run_bind_ok (evalE 1 (.int p i) env) (fun b => whnf 1 b) m m' a heval]
    exact hwhnf
  rw [demand]
  change
    ((ExceptT.tryCatch (evalE 1 (.int p i) env >>= fun b => whnf 1 b)
      (fun h : Halt => throw (h.attach p))).run).run m =
      (Except.ok (.int i), m')
  simp only [ExceptT.tryCatch, ExceptT.run, ExceptT.mk, StateT.run_bind]
  rw [hbody]
  rfl

/-- `demand` の具体的な終了状態（初期 Heap に整数値 42 の `done` Cell を追加）。 -/
def memoWitnessAfterDemand : Machine :=
  let m := memoWitnessMachine.blackholed memoWitnessAddr memoWitnessExpr
  { m with heap := (m.heap.alloc (.done (.int 42))).1 }

/-- 初期 Cell は確かに `suspended`。P2a の割当補題を再利用する。 -/
theorem memoWitness_suspended :
    memoWitnessMachine.heap.cell? memoWitnessAddr =
      some (.suspended memoWitnessExpr memoWitnessEnv) :=
  Heap.alloc_cell?_new Heap.initial memoWitnessCell

/-- この実例は P2d-1 の構造的整合性も満たす。 -/
theorem memoWitness_structWF : memoWitnessMachine.heap.StructWF :=
  Heap.alloc_structWF Heap.initial memoWitnessCell Heap.initial_structWF

/-- 実際の評価器で `demand 2` が `ok (.int 42)` で終了する。
    上の `demand_int_ok` と、独立に記述した最終状態の定義で示す。 -/
theorem memoWitness_demand_ok :
    ((demand 2 memoWitnessExpr memoWitnessEnv).run).run
      (memoWitnessMachine.blackholed memoWitnessAddr memoWitnessExpr) =
        (Except.ok (.int 42), memoWitnessAfterDemand) := by
  simpa only [memoWitnessExpr, memoWitnessAfterDemand] using
    demand_int_ok (memoWitnessMachine.blackholed memoWitnessAddr memoWitnessExpr)
      { line := 1, col := 1 } 42 memoWitnessEnv

/-- P2d-5 の2前提を同時に満たす具体的な証人が存在する。
    さらに初期 Heap は `StructWF` を満たすので、恣意的な壊れた Heap ではない。 -/
theorem whnf_suspended_ok_memo_nonvacuous :
    ∃ n : Nat, ∃ a : Addr, ∃ e : Expr, ∃ env : Env,
      ∃ m : Machine, ∃ m₂ : Machine, ∃ v : Value,
        m.heap.StructWF ∧
        m.heap.cell? a = some (.suspended e env) ∧
        ((demand n e env).run).run (m.blackholed a e) = (Except.ok v, m₂) := by
  exact ⟨2, memoWitnessAddr, memoWitnessExpr, memoWitnessEnv,
    memoWitnessMachine, memoWitnessAfterDemand, .int 42,
    memoWitness_structWF, memoWitness_suspended, memoWitness_demand_ok⟩

/-- 上の実例に統合定理を適用した結果。再強制は任意の正の fuel で状態を変更しない。 -/
def memoWitnessMemoized : Machine :=
  { memoWitnessAfterDemand with
    heap := memoWitnessAfterDemand.heap.setCell memoWitnessAddr (.done (.int 42)) }

theorem memoWitness_integrated :
    ((whnf 3 memoWitnessAddr).run).run memoWitnessMachine =
      (Except.ok (.int 42), memoWitnessMemoized) ∧
    memoWitnessMemoized.heap.cell? memoWitnessAddr = some (.done (.int 42)) ∧
    ∀ k, ((whnf (k + 1) memoWitnessAddr).run).run memoWitnessMemoized =
      (Except.ok (.int 42), memoWitnessMemoized) :=
  whnf_suspended_ok_memo 2 memoWitnessAddr memoWitnessExpr memoWitnessEnv
    memoWitnessMachine memoWitnessAfterDemand (.int 42)
    memoWitness_suspended memoWitness_demand_ok

#print axioms whnf_suspended_ok_memo_nonvacuous
#print axioms memoWitness_integrated

end Les.Eval
