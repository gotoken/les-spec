# Corpus

English | [日本語](README.ja.md)

`*.les`: code to run, `*.stdin`: standard input (optional), `*.expect.json`: exact expected stdout / stderr / exit_code.

The initial cases are **not-yet-run candidates** selected from the upstream Go implementation and Go tests. Check them for real with `run.py` in P0, and if there is a mismatch, record the cause instead of simply accepting the observed output as the expectation. From now on, each case will be tagged with rule IDs.

## Matching stderr
`run.py` replaces the absolute path of the case file in stderr with `<CASE>` before comparing with the expectation. Error cases put `stderr` in the expectation and compare it exactly (a matching exit code alone is not a PASS).

## Semantic tests and rule IDs (P1c-3)

`rules` in `*.expect.json` are the rule IDs from section 2.1 of `docs/evaluator-design.md` (not read by `run.py`). Expectations were written first from the predictions in the design notes, then checked against the Go CLI at the pinned commit (the oracle). Variable declarations use type annotations to eliminate `Type Warning`s (that this does not change behavior was confirmed by running unannotated versions with the CLI: `t5` / `t6` / `t18` in the design notes).

| Case | Rule ID | Ledger | Description |
|---|---|---|---|
| `rebind-forces-rhs` | E3 | LZ-004 | Rebinding forces the right-hand side on the spot (lazy for an initial binding) |
| `rebind-old-binding` | E4 | LZ-004 | The right-hand side of a rebinding refers to the old binding (`5` → `+1` → `*2` = `12`) |
| `rebind-discards-thunk` | E5 | LZ-004 | An old thunk that was rebound away is not evaluated |
| `snapshot-late-rebind` | E14 | LZ-005 | A thunk snapshots the bindings at creation time (later rebindings are not visible) |
| `forward-ref` | E15 | LZ-005 | Names unbound at creation time are looked up at evaluation time (forward reference) |
| `forward-ref-rebound` | E15 | LZ-005 | A forward reference sees the **latest** binding at evaluation time (`a = 5` → `a = 7` gives `8`) |
| `memo-binding` | E9 | LZ-003 | A bound thunk is shared and memoized (side effect happens once) |
| `arg-sharing` | E10 | LZ-003 | An argument is shared with the parameter (the side effect of `twice(g())` happens once) |
| `blackhole` | E16 | LZ-003 | A self-referential thunk is a blackhole (error without position; output is kept) |
| `exit-lazy` | E20 | EX-001 | `exit` terminates when demanded; output up to that point is kept |
| `error-keeps-output` | E19, E21 | EX-001, ER-001 | Output is kept even on a runtime error. The position is that of the expression of the thunk being forced |
| `error-pos-bare-stmt` | E21 | ER-001 | An error outside any thunk is at the start of the statement |

### Additions (E2, E11–E13, E17, E22)

Each case is built so that **a different evaluation strategy would change the output**. The "What it distinguishes" column says how the output would change under that strategy.

| Case | Rule ID | Ledger | What it distinguishes (expected stdout) |
|---|---|---|---|
| `order-binary-operands` | E17 | ORD-001 | `print a() + b()` (`a` / `b` print): left to right gives `a;b;3`, right to left gives `b;a;3` |
| `order-print-args` | E17, E19 | ORD-001 | `print a(), b()`: forces all arguments before writing, so `a;b;12`. An implementation that writes each argument as it goes gives `a;1b;2`; right to left gives `b;a;21` |
| `order-binary-abort` | E17, E21 | ORD-001 | If the left (`a`) fails, the right (`b`) is not evaluated: stdout `a;`, `:3:` col 5 (start of the statement inside the function). Right to left gives `b;a;` |
| `live-global-in-function` | E13 | FN-001 | A function body sees globals rebound after definition: `3;4`. A snapshot at definition time gives `3;3` |
| `ident-arg-not-forced` | E11 | FN-001 | An identifier argument is not forced at call time (`n = 1 / 0`, `k(n)` where `k` does not use its argument): `1`. An implementation that evaluates arguments eagerly errors |
| `ident-arg-shares-cell` | E11 | FN-001 | An identifier argument is the same cell as the caller's binding: the result forced in the callee is shared, giving `side;21`. Copying would run the side effect twice; call-by-name would run it twice inside the callee |
| `call-local-rebind` | E12 | FN-001 | `x = 2` inside a function is a local binding: `2;1`. An implementation that writes to the global gives `2;2` |
| `call-body-last-value` | E12 | FN-001 | All statements of the body run in order, and the value is the last expression statement: `a;b;3` |
| `alias-binding-not-forced` | E1, E2 | LZ-001, LZ-006 | `m = n` (with `n = 1 / 0`) does not force `n`: `ok`. **E1 and E2 cannot be shown separately** (note at the end of section 2.1 of the design notes) |
| `ident-stmt-forces` | E22 | LZ-006 | A statement consisting of a single identifier forces the variable: `n = 1 / 0`⏎`n` errors (`:1:` col 7). An implementation that does not force gives `ok` |
| `ident-stmt-calls-function` | E22 | LZ-006 | If a statement consisting of a single identifier is a `def`, it is called with 0 arguments: `hi;end`. An implementation that does not call it gives `end` |

### Additions (P1c-6: parent scope of closures, environment capture of argument thunks)

| Case | Rule ID | Ledger | What it distinguishes (expected stdout) |
|---|---|---|---|
| `closure-defining-scope` | E12, E13 | FN-001 | `y = 3`, `def f(): y`, `def g(): y = 99; f()`: the parent of `f` is the **scope at definition time**, so `3`. Using the caller (the child scope of `g`) as the parent gives `99` |
| `arg-thunk-snapshot-env` | E11, E14 | LZ-005, FN-001 | `a = 1`, `def f(p): p`, `b = f(a + 1)`, `a = 10`, `print b`: the argument thunk captures from the `snap` of `b`'s thunk (`a` = the old binding), so `2`. Looking only at the live scope gives `11` |

**Observational limit (`arg-thunk-snapshot-env`)**: This case distinguishes an implementation that "ignores `snap` and looks only at the live scope," but does **not distinguish** an implementation that "re-`capture`s the argument thunk" from one that "uses `suspended a env` as is" (both give `2`). No distinguishing example has been found.

**Observational limit**: E2 (referencing a variable as an expression does not force it) and E12's "unevaluated return value" cannot be demonstrated independently within the 9 nodes. In lazy positions E1 and E11 give the same results, in strict positions the consumer forces, and a statement consisting of a single identifier forces by E22. We do not claim to have demonstrated E2 as an independent rule.

The rule IDs of the 10 existing cases (`basic-print` etc.) are mapped in `tasks/results/P1c-3.md` (Japanese).
