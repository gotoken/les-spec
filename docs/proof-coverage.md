# Results of P0–P2d-5 and proof coverage

English | [日本語](proof-coverage.ja.md)

Interim report as of 2026-11-15. The target is [`unak/les`](https://github.com/unak/les) at the pinned commit `aa78fdcfc76b156e6b5ab4735516fcefadce954b` ([`upstream/LES_COMMIT`](../upstream/LES_COMMIT)).

**Conclusion of this document:** From observations of the Go CLI, we built an executable Lean evaluator restricted to 9 syntax node kinds, and checked stdout, stderr, and exit code against expectations on 35 programs. Furthermore, **for that Lean model**, we proved basic Heap properties, name resolution, non-decrease of the number of cells, and memoization of a successful first force together with stability of re-forcing. **General equivalence between the Go implementation and the Lean model is not proved.**

> **Merge status:** P0–P2d-5 (including [PR #19](https://github.com/gotoken/les-spec/pull/19)) are merged into main (P2d-5 merge commit `12e9af9`). [PR #20](https://github.com/gotoken/les-spec/pull/20) added a witness that actually satisfies the P2d-5 hypotheses in [`lean/Les/Proofs/NonVacuity.lean`](../lean/Les/Proofs/NonVacuity.lean), and its initial build failure was fixed in [PR #22](https://github.com/gotoken/les-spec/pull/22). Both are merged into main (`43e8839`).

## 1. What was built and how far it works

| Step | Artifacts and status | Evidence |
|---|---|---|
| P0 | Pinned the target commit of the Go CLI, ran 5 oracle cases, Lean 4.25.0 / Lake 5.0.0 scaffolding | [P0](../tasks/results/P0.md) |
| P1a | Contrast experiments between lazy evaluation and explicit `force` / `!`. Path normalization and exact comparison of stderr | [P1a](../tasks/results/P1a.md) |
| P1b | `lesdump`, reusing the upstream Go parser and type checker. A fixed JSON AST format | [P1b](../tasks/results/P1b.md) |
| P1c-1–3 | Lean AST/JSON decoder, evaluator design, observed rules E1–E22, a Go CLI corpus of 33 cases | [Design notes](evaluator-design.md), [P1c-3](../tasks/results/P1c-3.md) |
| P1c-4–6 | Fuel-bounded Lean evaluator. Added `def`, closures, thunk sharing, and environment capture; passes 35 corpus cases and 41 unit tests | [P1c-5](../tasks/results/P1c-5.md), [P1c-6](../tasks/results/P1c-6.md) |
| P2a–P2c | Theorems on Heap operations, memoization, environment capture, and forward references | [`lean/Les/Proofs/`](../lean/Les/Proofs/) |
| P2d-1–4 | Structural Heap well-formedness, monotonicity of the number of cells in the evaluator, derivation of address validity after the first force | [P2d-3](../tasks/results/P2d-3.md), [P2d-4](../tasks/results/P2d-4.md) |
| P2d-5 | Integrated a successful first force, memoization, and re-forcing into one theorem (**PR #19, merged into main**) | [PR #19](https://github.com/gotoken/les-spec/pull/19), [results record (PR #19)](https://github.com/gotoken/les-spec/blob/6a7dbc2f651bbc4deaa4be661c86852989f5e6de/tasks/results/P2d-5.md) |

The step records under `tasks/results/` are in Japanese.

### Scope of the execution model

- The input is a `CheckedProgram` that has passed the Go parser and type checker. **The correctness of the type checker is not proved in Lean.**
- The Lean AST has 6 expression forms (Ident, Int, String, Binary, Force, Call) and 3 statement forms (ExprStmt, VarDecl, FuncDef). This is not the full syntax of Les.
- `Heap` is an array of cells and scopes. It distinguishes unevaluated `suspended`, under-evaluation `blackhole`, and evaluated `done`, and cell addresses are shared.
- `Env` holds `snap`, a map from captured names to addresses, and a reference to a live scope. Captured names are resolved via `snap` first; uncaptured names are looked up in the scope.
- `EvalM = ExceptT Halt (StateM Machine)`. Changes to the Heap and stdout made up to that point survive an abnormal termination. Recursion is bounded by fuel, but fuel is not an upper bound on the total number of steps.
- Remaining unsupported features include Tuple, Dict, `if`, patterns, struct, full type inference, and some cases of division of negative numbers.

### What the tests do and do not confirm

- The 35 cases of the [Go CLI corpus](../difftest/corpus/) were observed at the pinned commit, and the Lean evaluator produced the same expected stdout, stderr, and exit_code (reported as PASS 35 / FAIL 0 / OUT_OF_FUEL 0 / UNSUPPORTED 0).
- There are [execution records for each step](../tasks/results/P1c-6.md) showing that 41 Lean unit tests, AST decoding and round-tripping, and the Go oracle differential check (35/35) succeeded. We also confirmed that deliberate changes make tests fail (e.g., the parent scope of a closure, the `snap` of a thunk, evaluation order).
- This is **observational agreement on a finite set of programs**, not equivalence of Lean and Go on all inputs. These records also do not support a claim of independent continuous verification on GitHub Actions.
- Each PR has execution records of the build and `#print axioms` showing proofs without `sorry` / `admit` / new axioms. However, stating this in a document does not constitute new independent verification.
- AI token usage is **not measured**. There is no measured comparison of cost or of advantages over manual work.

## 2. Language rules E1–E22 and the boundary of formal guarantees

Legend: **observation** means checks against the pinned Go CLI or `lesdump`; **execution check** means comparing Lean execution results with expectations for the corresponding restricted syntax; **direct theorem** means part of the behavior was proved as a universally quantified statement in Lean. Even when an ID is marked as "has a theorem," not every aspect of the rule has been proved. For the exact scope of each original rule and reproduction examples, see the [evaluator design notes](evaluator-design.md) and the [corpus mapping table](../difftest/corpus/README.md).

| Rule | Target of observation / execution check (sublanguage) | Direct proof in Lean and remaining boundary |
|---|---|---|
| E1 Initial binding is lazy | An unused `1 / 0` is not executed | No general theorem about variable declarations |
| E2 Identifier references are not forced in principle | Observed in combination with E1 and E11. **Not identified as an independent rule** | Not proved |
| E3 Rebinding evaluates the right-hand side immediately | Contrast with an initial binding that divides by zero | Evaluation timing of rebinding in general not proved |
| E4 The right-hand side of a rebinding refers to the old binding | `x = x + 1` etc. | Not proved |
| E5 A discarded old thunk is not needed | The old `1 / 0` is not used | Not proved |
| E6 Forcing with `force` / `!` | Contrasted for both bindings and arguments | General forcing boundary not proved |
| E7 Associativity of `force` | Checked via the Go parser AST and Lean JSON round trip | Correctness of parsing not proved |
| E8 Whether forced or not, and the value | Compared on corresponding examples | General identity of values not proved |
| E9 Memoization of shared thunks | Examples where a side effect happens once, etc. | **Proved**: `whnf_done`, `whnf_suspended_ok_*`, PR #19 `whnf_suspended_ok_memo`. **Assumes a successful demand** |
| E10 Call-by-need sharing of arguments | The side effect of `twice(g())` happens once | No general theorem about argument preparation or whole function calls |
| E11 Identifier arguments share the existing cell | Observed unused arguments and sharing after forcing | There are lemmas about `lookupEnv`, but argument sharing as a whole is not proved |
| E12 Closure body and local scope | Last expression statement, local rebinding, parent scope | Semantic correctness of whole calls not proved |
| E13 The live scope at definition time | Global rebinding after definition, etc. | Closure behavior as a whole not proved |
| E14 Bindings visible at capture time are fixed | `b = a + 1; a = 10` uses the old reference | **Proved**: `capture_preserves` / `capture_preserves_under_bind`. What is preserved is the **address**, not permanent immutability of cell contents |
| E15 Forward reference of uncaptured names | Bindings and rebindings after creation | **Proved**: `capture_unbound_lookup`, `forward_ref_resolves`, `forward_ref_rebound`. Subject to conditions such as existence of the target scope |
| E16 Blackhole | Error from self-reference, stdout preserved | **Partially proved**: `whnf_blackhole`, `whnf_reenter_blackholed`. Cycle detection along arbitrary execution paths not proved |
| E17 Left-to-right forcing order | Arithmetic and `print`; if the left operand fails the right is not executed | Execution checks only. No general evaluation-order theorem |
| E18 Integer arithmetic and division by zero | `n / 0` and some integer operations | Division of negative numbers etc. unsupported and unverified. No general theorem |
| E19 `print` and output retention | Output without newline after forcing all arguments | No general theorem on output order or output retention on exceptions |
| E20 `exit` terminates on demand | Unevaluated `exit` and output retention | Some values such as Bool unsupported. No general theorem |
| E21 Error positions | Innermost forcing point / start of statement, etc. | General correctness of positions not proved |
| E22 Statements consisting of a single identifier | Forced, and called with 0 arguments if a closure | Zero-argument calls of builtins unsupported. No general theorem |

In particular, **E2 cannot be distinguished observationally from E1/E11**, and the "unevaluated return value" of E12 also cannot be distinguished independently with the current 9 nodes. Before adding syntax or evaluator features, keep this kind of **observational distinguishability** in mind.

## 3. Proved properties and their hypotheses

| Step / Lean source | Main theorems | What can be claimed |
|---|---|---|
| [P2a: Heap](../lean/Les/Proofs/Heap.lean) | `Heap.alloc_cell?_of_valid`, `Heap.setCell_cell?_ne`, `Heap.bind_cell?`, `Heap.bind_lookupLocal_self` | Local properties of cell allocation, update, and binding. Subject to each theorem's hypotheses, such as the update target and address validity |
| [P2b: Memo](../lean/Les/Proofs/Memo.lean) | `whnf_done`, `whnf_blackhole`, `whnf_suspended_ok`, `whnf_suspended_ok_cell_valid` | Re-forcing `done` changes nothing; re-forcing an existing `blackhole` is an error. After a successful `demand` the cell becomes `done` |
| [P2c: Capture](../lean/Les/Proofs/Capture.lean) | `capture_preserves`, `forward_ref_resolves`, `forward_ref_rebound` | Captured addresses are fixed; uncaptured names are resolved from the live scope. Does not include immutability of cell contents or well-formedness of the whole Heap |
| [P2d-1: WellFormed](../lean/Les/Proofs/WellFormed.lean) | `Heap.initial_structWF`, `Heap.alloc_structWF`, `Heap.setCell_structWF`, `Heap.newScope_structWF`, `Heap.bind_structWF` | `StructWF` consists only of 3 conditions: scope binding targets, parents, and decreasing parent indices. `bind` needs validity of the new address, `newScope` needs validity of the parent, etc. |
| [P2d-2: Monotone](../lean/Les/Proofs/Monotone.lean) | `mono_bind`, `mono_tryCatch`, `mono_validAddr`, `modHeap_not_mono` | Composes **non-decrease of the number of cells in the final state**. Does not claim that an arbitrary `modHeap f` is monotone; there is a counterexample |
| [P2d-3: MonotoneEval](../lean/Les/Proofs/MonotoneEval.lean) | `monoAt`, `demand_mono`, `evalE_mono`, `whnf_mono`, `demand_validAddr` | Uses fuel induction over the 11 mutually recursive functions of the actual evaluator. Valid addresses are preserved up to the final state of both normal and abnormal termination |
| [P2d-4: Memo](../lean/Les/Proofs/Memo.lean) | `Machine.blackholed_validAddr`, `demand_blackholed_validAddr`, `whnf_suspended_ok_then_stable_valid` | Uses the existence of the initial `suspended` cell and the success of `demand` to connect to the memoization theorem without assuming the former `hvalid` externally |
| [P2d-5: PR #19](https://github.com/gotoken/les-spec/pull/19) | [`whnf_suspended_ok_memo`](https://github.com/gotoken/les-spec/blob/6a7dbc2f651bbc4deaa4be661c86852989f5e6de/lean/Les/Proofs/Memo.lean) | **On main.** Integrates success of the first force, writing `done`, and stability of re-forcing with any positive fuel, without external `hrun` / `hvalid` hypotheses |

### The P2d-5 integrated theorem: exact conditions

The theorem `whnf_suspended_ok_memo` requires the following two hypotheses.

1. `m.heap.cell? a = some (.suspended e env)` (the target cell is unevaluated at the start)
2. `((demand n e env).run).run (m.blackholed a e) = (Except.ok v, m₂)` (demand from the blackholed state terminates normally)

With `m₃ := { m₂ with heap := m₂.heap.setCell a (.done v) }`, the conclusion is:

- Running `whnf (n + 1) a` yields `(Except.ok v, m₃)`.
- `m₃.heap.cell? a = some (.done v)`.
- For every `k : Nat`, running `whnf (k + 1) a` from `m₃` yields `(Except.ok v, m₃)`; that is, neither the value nor the Machine changes.

**This is not a theorem that demand always succeeds.** Also, monotonicity is a statement about the number of cells in the final state; it does not directly state an invariant of all intermediate states.

### An example showing non-vacuity of P2d-5 (added in PR #20)

[`lean/Les/Proofs/NonVacuity.lean`](../lean/Les/Proofs/NonVacuity.lean) allocates, on the existing `Heap.initial`, an unevaluated cell holding the integer literal `42`, and shows the following for the same concrete Machine.

- `memoWitness_suspended`: the cell at the allocated address is `.suspended e env`.
- `memoWitness_structWF`: the Heap of this Machine satisfies the existing `Heap.StructWF` (structural well-formedness of scopes).
- `memoWitness_demand_ok`: from the state where that cell is rewritten to `blackhole`, `demand 2 e env` terminates with `Except.ok (.int 42)`. This computes the actual Lean evaluator by `rfl`.
- `whnf_suspended_ok_memo_nonvacuous`: shows, as an existence theorem together with `StructWF`, **the existence of a witness for which the two hypotheses of P2d-5 hold simultaneously**.
- `memoWitness_integrated`: applies the existing `whnf_suspended_ok_memo` to the witness, showing success of the first force, writing `done`, and stability of re-forcing with any positive fuel.

**This witness confirms that "an example satisfying the conditions exists"; it is not a claim that every `demand` succeeds.** Also, `StructWF` is not full Heap well-formedness covering references inside cells.

**Verification record (2026-11-15):** PR #20 had been merged into main, but the first `lake build` failed on the `rfl` of `memoWitness_demand_ok`. The fix is in [PR #22](https://github.com/gotoken/les-spec/pull/22), and `lake build` with Lean 4.25.0 succeeded in a [GitHub Actions run](https://github.com/gotoken/les-spec/actions/runs/43715079526). `#print axioms` for the new theorems shows only `propext` / `Quot.sound` (no `sorryAx`). PR #22 was merged into main on 2026-11-15, and [CI on main](https://github.com/gotoken/les-spec/actions/runs/43715625663) for the merge commit `43e8839` also succeeded.

## 4. Dependencies

The diagram below summarizes the main semantic dependencies; it is not a one-to-one map of Lean `import`s.

~~~mermaid
flowchart TD
    A["P2a: local Heap lemmas"]
    B["P2b-1/2: case analysis of whnf and stability of done"]
    C["P2c-1/2: capture / lookupEnv"]
    D["P2d-1: StructWF and basic operations"]
    E["P2d-2: monotonicity of cell count and composition"]
    F["P2d-3: 11 mutually recursive functions, demand_mono"]
    G["P2d-4: ValidAddr after demand"]
    H["P2d-5: integrated theorem on memoization on success (main)"]
    I["PR #20: concrete witness of non-vacuity"]
    A --> B
    A --> C
    A --> D
    A --> E
    E --> F
    F --> G
    A --> G
    B --> G
    B --> H
    G --> H
    A --> I
    D --> I
    H --> I
~~~

Environment capture in P2c and address validity in P2d are currently proved as **separate properties**. Together they do not guarantee correctness of the language as a whole.

## 5. Open verification tasks (stating what is not yet achieved)

### Audits to do first

1. **Non-vacuity (witness added, fixed in PR #22):** Constructed in [`NonVacuity.lean`](../lean/Les/Proofs/NonVacuity.lean) a concrete `Machine` / `Expr` / `Env` / fuel that simultaneously satisfies the P2d-5 hypotheses `h` and `hd`. The original `rfl` failure was fixed in PR #22, and CI confirmed Lean compilation and `#print axioms`.
2. **Checking correspondences:** When temporary semantic modifications are made to the evaluator, check where the corresponding differential tests or theorems detect them. Also check that the hypotheses of the proofs have not become trivial.
3. **Reproducibility of the theorems:** PR #19 / #20 / #22 are merged into main. A [GitHub Actions run](https://github.com/gotoken/les-spec/actions/runs/43715625663) (Lean 4.25.0) on the main merge commit `43e8839` succeeded with `lake build`, the 35 comparisons and unit tests, and `#print axioms`. Reproduction from a fresh local clone and running the Go CLI oracle will be confirmed separately.

### Next semantic questions

- What remains in cells/blackholes and stdout when `demand` ends with an error or `outOfFuel`. Do not extend the memoization theorem for success directly to failure.
- Stronger Heap well-formedness covering `Env.snap` / `Env.scope` in `Cell.suspended` and the scope of `Value.closure`, and its **preservation along every execution path of the evaluator**. Preservation of `StructWF` alone is not enough.
- Extensions of syntax and execution features (`if`, Tuple, Dict, patterns, etc.) proceed one feature at a time in the order observation → rule → Lean model → differential test → necessary proofs.
- General equivalence of Go and Lean, Go's type inference and type safety, and correctness of all features are long-term goals and are not part of the current results.

## 6. Entry points to the plan change and reproduction steps

The original [`PLAN.md`](../PLAN.md) assumed "P2 = feature extension, P4 = theorems." In practice, since P1 produced an executable (if limited) model and 35 oracle comparisons, we changed the order to **freeze that model and prove the core theorems first**. See the updated [PLAN.md](../PLAN.md) for the reasons and the mapping between old and new phases.

~~~sh
bash scripts/bootstrap.sh
python3 difftest/run.py
python3 lesdump/test.py
cd lean
lake build
lake exe les-syntax-test ../lesdump/golden 35
lake exe les-eval-test ../lesdump/golden ../difftest/corpus
~~~

These commands are reproduction steps, **not results re-run by the PR that created this document**. Individual execution results are recorded in `tasks/results/`.
