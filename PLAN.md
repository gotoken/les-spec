# Plan: from the observable semantics of les to a Lean formalization

English | [日本語](PLAN.ja.md)

> **Revised 2026-11-15:** We prioritized formal proofs about the small evaluator that worked in P1 over the feature additions originally planned for P2. The old plan is kept explicitly as the history of this revision. P0–P2d-5 are on main (including [PR #19](https://github.com/gotoken/les-spec/pull/19) with the integrated theorem). [PR #20](https://github.com/gotoken/les-spec/pull/20) is also merged into main; however, the first build revealed a problem in the proof, which was fixed in [PR #22](https://github.com/gotoken/les-spec/pull/22) and merged into main on 2026-11-15 (CI on main also passes). See [Results of P0–P2d-5 and proof coverage](docs/proof-coverage.md) for the detailed scope of what has been achieved.

## History of plan changes and reasons

| Item | Original (as of P0) | As organized on 2026-11-15 |
|---|---|---|
| P0 | Go CLI oracle and Lean scaffolding | Done. Pinned SHA, reproduction commands, and a minimal corpus established |
| P1 | One full round of a small lazy-evaluation rule | Done. Expanded to 9 syntax node kinds, 35 Go/Lean comparisons, and 41 unit tests |
| **P2** | Feature additions: Tuple / Dict / closure / patterns / struct, etc. | **Reordered: prove formal properties of Heap, Thunk, and environment capture first** (P2a–P2d-5) |
| "Theorems" in old P4 | To be considered once the model was stable enough | **Done early, with the scope stated explicitly, as soon as a restricted core model worked** |
| New P3 (planned) | Corresponds to old P2 | Extend one feature at a time: observation → rule → Lean → differential check → necessary theorems. Timing and priority undecided |
| New P4 / P5 (planned) | Old P3 (types), old P4 (peripheral features) | Candidates: involvement of types, other features, stronger equivalence checking. Not started automatically |

**Why we proved things first:**

1. P1 succeeded on 35 oracle comparisons and produced a **small executable model** with `Heap`, `whnf`, and `capture`. Before adding more features, we were in a position to pin down the invariants this model has.
2. The Les-specific contrast that **captured names keep seeing old addresses while uncaptured names see new bindings** (E14/E15), and memoization of shared thunks (E9/E16), are worth verifying more strongly than by matching examples.
3. Attempting theorems reveals the hypotheses they need. For example, `bind` to an invalid address breaks well-formedness, and address validity after `demand` could be derived from the evaluator's monotonicity in the number of cells. We came to understand the dependencies in the Heap design before any large feature extension.
4. Rather than a large bulk port, **splitting work into small PRs and proceeding implement → test → prove → record → review → stop** leaves verifiable results at each stage. There is no measured comparison yet showing this is cheaper, and token usage is not measured.

**What changed is the order of work, not a disguised change of the target scope.** Equivalence of Go and Lean on all programs, correctness of Go's type inference, and type safety of Les as a whole remain unproved. The P2 proofs hold for the existing Lean model; generalizing them to Go requires separate evidence.



## Goals and non-goals

The target is the observable behavior of `unak/les` at a **pinned commit**. Rather than a line-by-line port of the Go implementation, we build a small semantics that explains inputs, stdout, stderr, exit codes, and, where needed, the order of effects during evaluation.

- First reproducible observations, then an executable model in Lean, and finally the theorems we need.
- We do not assume the existing implementation is correct. Discrepancies are classified as "model error / unspecified behavior / oracle path difference / suspected Go issue."
- At the start of P0 we prioritized one small round trip, and did not begin a full feature inventory, a full port of type inference, or theorem proving. After P1 was complete we changed priorities and moved on to the P2 proofs. Where usage could not be measured, it is marked "not measured."
- We do not reimplement parsing in Lean. The current pipeline is Go parser and type checker → `lesdump` JSON → Lean AST decoder.

## Phases and completion criteria

### P0: A reproducible oracle and minimal Lean scaffolding

1. Pin `upstream/LES_COMMIT` and build the Go CLI locally.
2. Run the minimal examples in `difftest/corpus` with the CLI and record stdout / stderr / exit code. Go's `eval_test.go` is a reference for the specification and is not treated as identical to the CLI.
3. If Lean / Lake is available, create a minimal project and record how to reproduce `lake build`. If not installed, document the steps and mark P0 as partially complete.
4. Record measured run time, number of conversation turns / tool calls, and usage if available in `tasks/results/`, and **stop here once**.

Done when: the pinned commit is confirmed, the known Go CLI tests pass, and open items and instructions for resuming are recorded. If Lean is not installed, do not pretend the build succeeded.

### P1: One full round of a lazy-evaluation rule in Lean

The first targets are integers, variable bindings, function arguments, `print`, and call-by-need evaluation. Confirm with minimal examples the result of `choose(42, 1 / 0)` and the difference made by forcing.

On the Lean side, keep definitions to the necessary minimum, such as `Expr` / `Value` / `Env` / `Heap` / `Outcome`. Thunks represent unevaluated, being evaluated, and evaluated, without forgetting sharing of evaluation. First make a fuel-bounded evaluator that can be compared differentially, and write no theorems yet.

Done when: Lean execution and differential tests correspond to a handful of Go CLI experiments, and the ledger is updated with evidence. If failures remain, save minimal counterexamples.

### P2: Proofs about the core operational semantics (changed from the original P2)

**Record what has been done and its merge status separately.** The proofs are about the existing definitions in `lean/Les/Eval/`, not about general equivalence with the Go implementation.

| Step | Proofs / results | Status |
|---|---|---|
| P2a | Basic lemmas for `Heap.alloc` / `setCell` / `bind` | On main ([PR #10](https://github.com/gotoken/les-spec/pull/10)) |
| P2b-1/2 | The `done` / `blackhole` / `suspended` branches of `whnf`, first force and re-force | On main ([PR #11](https://github.com/gotoken/les-spec/pull/11), [PR #12](https://github.com/gotoken/les-spec/pull/12)) |
| P2c-1/2 | Preservation of addresses captured in `snap`; forward reference and rebinding of uncaptured names | On main ([PR #13](https://github.com/gotoken/les-spec/pull/13), [PR #14](https://github.com/gotoken/les-spec/pull/14)) |
| P2d-1 | `Heap.StructWF` and its preservation by basic operations (references inside cells not included) | On main ([PR #15](https://github.com/gotoken/les-spec/pull/15)) |
| P2d-2/3 | Composition lemmas for `Mono`, fuel induction over 11 mutually recursive functions, `demand_mono` / `demand_validAddr` | On main ([PR #16](https://github.com/gotoken/les-spec/pull/16), [PR #17](https://github.com/gotoken/les-spec/pull/17)) |
| P2d-4 | Derive valid addresses after `demand` finishes, removing the `hvalid` hypothesis | On main ([PR #18](https://github.com/gotoken/les-spec/pull/18)) |
| P2d-5 | Integrate success of the first force, `done` memoization, and stability of re-forcing into `whnf_suspended_ok_memo` | On main ([PR #19](https://github.com/gotoken/les-spec/pull/19)) |

When claiming P2 is complete, **attach the scope and unproved items from `docs/proof-coverage.md`**. In particular, success of `demand` itself, memoization after failure, full well-formedness of references inside `Cell`, and Go / Lean equivalence are unproved.

### P2 retrospective and audit (candidate next work, not started)

1. Added a **concrete witness** simultaneously satisfying `h` and `hd` of P2d-5 to [`NonVacuity.lean`](lean/Les/Proofs/NonVacuity.lean) (PR #20). **The initial build failure was fixed in PR #22, and the build and axiom check succeeded on GitHub Actions.**
2. Audit which of rules E1–E22 were observed with the oracle and which became universally quantified theorems in Lean ([results document](docs/proof-coverage.md)).
3. PR #19 / #20 / #22 are merged. [CI](https://github.com/gotoken/les-spec/actions/runs/43715625663) on the main merge commit `43e8839` confirmed `lake build`, the 35 comparisons and unit tests, and `#print axioms`. Reproduction from a fresh local clone will be checked separately.
4. As the next proof targets, consider the state of thunks / blackholes after failure, and well-formedness of references inside cells together with its preservation by the evaluator.

This section lists **candidates, not instructions to start work**. What to do next will be decided after review.

### P3: Add language features one at a time (old P2, not started)

Revisit the items listed in the old P2: Tuple, Dict, closures, patterns, control escapes (return/break/exit), struct, and so on. **The minimal part of closures and `exit` were already implemented in P1**, so only the unsupported parts are in scope. Priority, including new candidates such as `if`, is undecided.

Proceed one feature at a time: **Go CLI observation → record rules and counterexamples → add to the Lean AST / execution model → differential check → prove necessary invariants**. Do not run a full inventory in one go. Keep the current 35 cases passing.

### P4: Involvement of types (old P3, not started)

Go's `InferProgram` is called before CLI execution, and type information is also used during evaluation. Initially, target only the operational semantics of "inputs accepted by the Go CLI." Explicitly bring `is`, type patterns, generics, and type-dependent behavior into scope later. Do not start by porting the whole inferencer. **`CheckedProgram` is a boundary where we trust Go's type checking; it is not a type-safety theorem in Lean.**

### P5: Peripheral features and stronger verification (old P4, not started)

import, I/O, regular expressions (to the extent they can be treated as external primitives), Float, etc. Candidates include additional theorems such as determinism and type safety of the target sublanguage, and stronger Go/Lean verification using generated tests and correspondences. We do not treat the correctness of the Go implementation itself as proven.


## Work units and token-saving principles

- 1 task = 1 narrow question / 1 group of rules / a few tests. Write results to files instead of rereading known code repeatedly.
- Do not read the whole source. Narrow down to the relevant Go functions, AST cases, and related tests.
- **Sonnet is the point of contact**; Opus is called only when there are incompatible candidate interpretations, the specification and implementation contradict each other, or a Lean modeling choice is a branch that would be costly to undo.
- What is passed to Opus: the question, a minimal counterexample, relevant function names and line ranges, candidates A/B, and the decision needed. Output only the key points. In P0, zero calls in principle, and at most one if absolutely necessary.
- Builds, tests, diff extraction, and log compression are done by ordinary programs. Do not paste full success logs back into the model.
- At most 3 fix attempts for the same failure. If unresolved, record how to reproduce the failure and move on.
- GitHub is used only for periodically saving results. Communication between agents happens locally through `tasks/` and `ledger/`.
- When token counts are not available in the environment, write **not measured**. Do not call estimates measurements.

## Priority of evidence and observability

1. CLI execution results at the pinned commit (observations on the Go side)
2. Implementation code of individual Go functions
3. Existing Go tests (those calling `EvalProgram` directly take a different path from the CLI)
4. Explanations and inferences such as the README

A rule is called "confirmed" only when its scope, implementation evidence, and a reproduction test are presented. A single passing test is not taken as a general theorem or a complete specification.

Each test stores source, stdin, stdout, stderr, and exit code separately. `difftest/run.py` checks the Go CLI expectations, and separately `lake exe les-eval-test` compares the Lean evaluator against the expectations of the same corpus. Both passing is **agreement on a finite number of inputs**, not a proof of equivalence.
