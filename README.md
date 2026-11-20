# les-spec

English | [日本語](README.ja.md)

An experiment in inferring a small operational semantics from the **observable behavior of [unak/les](https://github.com/unak/les) at a pinned commit**, and building an executable evaluator and theorems about it in Lean.

This is not a line-by-line port of the Go implementation. We keep a clear distinction between proofs about the Lean model and **agreement on a finite set of tests** between the Go CLI and the Lean evaluator.

> The project was written up in Japanese first. The documents linked below have English translations; the Japanese originals (`*.ja.md`) are authoritative if the two disagree. Per-step work logs under `tasks/results/` and the AI working instructions are available in Japanese only.

## Current status (2026-11-15)

- Target Les commit: [`upstream/LES_COMMIT`](upstream/LES_COMMIT) (`aa78fdcf…`)
- Pipeline: JSON AST from `lesdump` (which reuses the Go parser and type checker) → decoded in Lean → run on a fuel-bounded evaluator
- For a restricted syntax of 6 expression forms and 3 statement forms: **35 Go/Lean observation comparisons PASS** and **41 Lean unit tests PASS** (per the execution logs of each step)
- Proofs about the Lean model: Heap operations, memoization of thunks, environment capture and forward references, structural Heap well-formedness, and monotonicity of the number of cells
- Merged into main up to the P2d-5 integrated theorem on memoization after a successful force ([PR #19](https://github.com/gotoken/les-spec/pull/19))
- [PR #20](https://github.com/gotoken/les-spec/pull/20) added non-vacuity theorems with a concrete witness in [`NonVacuity.lean`](lean/Les/Proofs/NonVacuity.lean) (merged into main; the initial build failure was fixed in [PR #22](https://github.com/gotoken/les-spec/pull/22), also merged into main and verified by CI on main)

See **[Results of P0–P2d-5 and proof coverage](docs/proof-coverage.md)** for details, and **[PLAN.md](PLAN.md)** for why the plan changed and the tentative next steps.

**Not proved:** general semantic equivalence of Go and Lean, correctness of Go's type inference, type safety of Les as a whole, full Heap well-formedness including references inside cells, among others.

## Reproducing the verification

Requirements: `git`, `go`, `python3`, Lean 4.25.0 / Lake (see `lean/lean-toolchain`).

~~~sh
git clone https://github.com/gotoken/les-spec.git
cd les-spec
bash scripts/bootstrap.sh
python3 difftest/run.py
python3 lesdump/test.py
cd lean
lake build
lake exe les-syntax-test ../lesdump/golden 35
lake exe les-eval-test ../lesdump/golden ../difftest/corpus
~~~

`difftest/run.py` checks the expected observations against the pinned Go CLI, and `les-eval-test` compares the Lean model against the same corpus expectations. For records of how many tests were actually run, see [P1c-6](tasks/results/P1c-6.md) (Japanese) and [P2d-5 (PR #19)](https://github.com/gotoken/les-spec/pull/19).

Fetching the Lean toolchain may be restricted in some environments. The workarounds used during the initial setup are recorded in [P0](tasks/results/P0.md) (Japanese) and [lean/README.md](lean/README.md).

## Repository guide

- [PLAN.md](PLAN.md): the original plan, why we switched to proofs first for P2 on 2026-11-15, and candidate next steps
- [docs/proof-coverage.md](docs/proof-coverage.md): results of P0–P2d-5, which of rules E1–E22 have proofs, theorem dependencies, and what remains unproved
- [docs/evaluator-design.md](docs/evaluator-design.md): evaluation rules E1–E22 derived from Go observations, and the evaluator design
- [ledger/rules.md](ledger/rules.md): a ledger of Go CLI observations with their evidence
- [upstream/LES_COMMIT](upstream/LES_COMMIT): the pinned Go upstream commit
- [difftest/](difftest/): Go CLI observations and normalized expected results
- [lesdump/](lesdump/): JSON serialization of the AST using the Go parser and type checker
- [lean/Les/Eval/](lean/Les/Eval/): the Lean evaluator
- [lean/Les/Proofs/](lean/Les/Proofs/): Lean theorems about the evaluator and Heap definitions. `NonVacuity.lean` gives a concrete example satisfying the P2d-5 hypotheses and applies the integrated theorem to it
- [tasks/results/](tasks/results/) (Japanese): per-step records of builds, tests, model usage, and open issues
- [CLAUDE.md](CLAUDE.md) (Japanese): basic policy for AI-driven work (small work units, stop conditions)
- [tasks/next.md](tasks/next.md) (Japanese): **a historical record of the initial P0 instructions**. Do not re-run it as a current work instruction

## About the next steps

The next language feature or proof target has not been decided yet. We will review the [results and proof coverage](docs/proof-coverage.md) and the P2d-5 non-vacuity proof, and then decide on the next task.

We do not start the next phase without approval; each task is executed, verified, recorded, and reviewed one at a time. Steps for which model usage could not be obtained are marked "not measured."
