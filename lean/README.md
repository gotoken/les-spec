# Lean implementation and proof layout (as of P2d-5)

English | [日本語](README.ja.md)

This directory contains a **limited executable evaluator** targeting a pinned commit of
[`unak/les`](https://github.com/unak/les), and Lean proofs about the definitions of that evaluator.
The P0-era description of "scaffolding only" and "evaluator and theorems to be implemented later" no longer applies.

For the scope of the results, the distinction between proved and unproved, and the table mapping rules E1–E22,
see [`docs/proof-coverage.md`](../docs/proof-coverage.md).

## Current file layout

~~~text
lean/
├── lean-toolchain            # Lean 4.25.0
├── lakefile.toml             # the Les library and two test executables
├── Les.lean                  # library entry point for syntax, evaluator, and proofs
├── Les/
│   ├── Syntax.lean
│   ├── Syntax/
│   │   ├── AST.lean          # 6 expression and 3 statement forms, type-check result, CheckedProgram
│   │   ├── Decode.lean       # lesdump JSON → Lean AST
│   │   └── Encode.lean       # AST → JSON (for round-trip tests)
│   ├── Eval/
│   │   ├── Types.lean        # Value, Cell, Env, Scope, Heap, Machine, Halt
│   │   ├── Heap.lean         # allocation, lookup, rebinding, parent-scope search
│   │   ├── Eval.lean         # fuel-bounded evaluator, thunks/closures, builtins
│   │   └── Observe.lean      # normalization of stdout/stderr/exit_code
│   └── Proofs/
│       ├── Heap.lean         # P2a: basic Heap operations
│       ├── Memo.lean         # P2b, P2d-4/5: first force, memoization, re-forcing
│       ├── Capture.lean      # P2c: lookup of captured / uncaptured names
│       ├── WellFormed.lean   # P2d-1: structural Heap well-formedness
│       ├── Monotone.lean     # P2d-2: composition lemmas for monotonicity of cell count
│       ├── MonotoneEval.lean # P2d-3: monotonicity of the evaluator's 11 functions
│       └── NonVacuity.lean  # P2d-5: a concrete example satisfying both hypotheses of the integrated theorem
└── Tests/
    ├── Main.lean             # decoding / re-encoding of the JSON AST, etc.
    └── Eval.lean             # comparison against the 35-case Go CLI corpus, and unit tests
~~~

The `Core/`, `Thm/`, `IO.lean`, and `Main.lean` envisioned at the start of P0 are not the actual layout.
The current names are `Syntax/`, `Eval/`, `Proofs/`, and `Tests/` as above.

## The evaluator and its boundaries

- It reads the `lesdump` JSON produced by the Go parser and type checker, and evaluates a `CheckedProgram`. Lean has not proved Go's type inference.
- The supported syntax is the **6 expression forms and 3 statement forms** needed by the current corpus. Les as a whole is not covered.
- `Env.snap` holds the name → cell address map captured at creation time; names that were not captured are resolved from the live scope.
- A cell is `suspended` / `blackhole` / `done`; `whnf` forces on demand and shares and memoizes successful results.
- The evaluator's recursion is stopped by fuel. Fuel is not the total number of execution steps.
- Since `EvalM = ExceptT Halt (StateM Machine)`, earlier changes to the Heap and stdout survive an exception.
- **The evaluator's `evalE`, `whnf`, `demand`, and the related mutually recursive functions are total definitions** and do not use `partial`. On the other hand, **the recursive JSON decoder and encoder do use `partial def`**. Do not confuse the two.

## Verification

In an environment with Lean 4.25.0 and Lake, run the following from the repository root.

~~~sh
bash scripts/bootstrap.sh
python3 difftest/run.py
python3 lesdump/test.py
cd lean
lake build
lake exe les-syntax-test ../lesdump/golden 35
lake exe les-eval-test ../lesdump/golden ../difftest/corpus
~~~

- `difftest/run.py` checks the oracle expectations against the pinned Go CLI.
- `les-eval-test` decodes the AST JSON, runs the Lean evaluator, and checks the observed results (stdout, stderr, exit_code) of all 35 cases against expectations. The 19 `stageA` cases are only a historical grouping in the output; all 35 cases, including stage B, must PASS.
- For the results of the 41 Lean unit tests and the syntax/decoding tests, see each step's record in `tasks/results/` (Japanese). The commands here are **reproduction steps**, not evidence of a re-run at the time this README was updated.
- `NonVacuity.lean` shows a concrete well-formed Heap satisfying the hypotheses of P2d-5's `whnf_suspended_ok_memo`, and the application of the integrated theorem. The same file also contains `#print axioms` check lines.

## What the proofs do and do not guarantee

Basic Heap operations, preservation of captured addresses and forward references of uncaptured names, monotonicity of the number of cells, memoization of a **successful** first force, and stability of re-forcing have been proved **for the definitions of this Lean evaluator**.

The following, however, are not guaranteed:

- Semantic equivalence with the Go implementation on all inputs (the 35 differential tests are finite observations).
- That every `demand` succeeds, or memoization after failure.
- Full Heap well-formedness including references inside cells. `StructWF` only covers the structure of scopes.
- Type safety or termination of the original Les as a whole.

For the setup in P0 and workarounds for fetching the Lean toolchain, see [`tasks/results/P0.md`](../tasks/results/P0.md) (Japanese).
