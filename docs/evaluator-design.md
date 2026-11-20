# Design notes for the Lean evaluator (P1c-2)

English | [日本語](evaluator-design.ja.md)

Status: **design only**. No implementation code, proofs, or added syntax support are included. The pinned upstream is `upstream/LES_COMMIT` (`aa78fdcf…`).
Here, "confirmed (CLI)" means an observation from actually running the Go CLI at the pinned commit, "confirmed (source)" means the result of a local reading of `.work/upstream-les/pkg/eval/`, and "undetermined" means checked by neither.

> Section numbers match the Japanese original, because comments in the Lean sources refer to them (e.g. "docs/evaluator-design.md section 4").

## 1. Positioning and trust boundary

- The input is `Les.Syntax.CheckedProgram` (`lean/Les/Syntax/AST.lean`). It carries a proof that `analysis.status = ok`, so a program with a type error cannot be passed at the type level.
- **`CheckedProgram` is a boundary where we trust the result "Go's type check passed"; it is not a type-safety proof in Lean.** The Lean side does not re-check types and does not read type annotations (strings). The evaluator is therefore made total so that it stops (`Halt.error`) even when it hits an "ill-typed operation." Where evaluation results depend on preconditions guaranteed by Go's type check (such as argument types), those preconditions are stated explicitly.
- The evaluator is a pure function `run : Nat → CheckedProgram → Outcome` that always terminates thanks to fuel. It performs no I/O and accumulates standard output as a string.
- The scope is only the 9 nodes of the current `lesdump` (`Ident` / `Int` / `String` / `Binary` / `Force` / `Call` / `ExprStmt` / `VarDecl` / `FuncDef`). The only builtins are `print` and `exit`.

## 2. Rules confirmed in the Go implementation

Terminology: Go's `Thunk` (`pkg/eval/value.go`) is `{Evaluated, Value, Expr, Env, Evaluating}`. `Force` evaluates an unevaluated thunk only once and stores the result; if it is demanded again while being evaluated, it panics with `blackhole`.

### 2.1 Confirmed rules

Minimal reproductions are written on one line with ⏎ standing for a newline. The position of `/` in the CLI column indicates the column number.

| ID | Rule | Minimal reproduction (observed) | Evidence |
|---|---|---|---|
| E1 | A variable binding creates an unevaluated thunk unless the right-hand side is **a literal or a Force**. If it is never evaluated, no error occurs either | `x = 1 / 0`⏎`print "ok"` → `ok`, exit 0 | CLI (`lazy-unused-binding`), source: `VarDecl` in `evalStmt` |
| E2 | Call-by-need: **referencing** a variable as an expression does not evaluate it (it is returned as a thunk). It is evaluated only when `print` / arithmetic / `exit` etc. demand a value. **Observationally indistinguishable from E1 (lazy binding) and E11 (identifier arguments)** (see the note at the end of 2.1). The exception is **a statement consisting of a single identifier**, which forces (E22) | `v = id(1 / 0)`⏎`print "after;"`⏎`print v` (`id(a) = a`) → stdout `after;`, division by zero at `print v` | CLI, source: `Identifier` in `evalExpr` (returns the result of `env.Get` as is). Corpus: `alias-binding-not-forced` (a combined check of E1 and E2) |
| E3 | **Rebinding** (`x = ...` to a name already in the same scope) **forces the right-hand side on the spot** and replaces the binding with the evaluated value. It is not deferred | `x = 1`⏎`x = 1 / 0`⏎`print "ok"` → error (`:2: division by zero at col 7`), exit 1, empty stdout. Contrast: the initial binding `x = 1 / 0` is not an error | CLI, source: the `if _, ok := env.store[s.Name]` branch of `VarDecl` (comment: to avoid circular references) |
| E4 | The right-hand side of a rebinding can refer to the **old binding** | `x = 1`⏎`x = x + 1`⏎`print x` → `2`. `x = 5`⏎`x = x + 1`⏎`x = x * 2` → `12` | CLI |
| E5 | An old thunk that was rebound away is not evaluated | `x = 1 / 0`⏎`x = 2`⏎`print x` → `2`, exit 0 | CLI |
| E6 | **Explicit force** (prefix `force e` and postfix `e!` are the same `Force` node) forces `e` **on the spot** when the expression it appears in is evaluated. At binding time for the right-hand side of a binding, at call time for an argument (even for an unused argument) | `x = (1 / 0)!`⏎`print "ok"` → error, exit 1 (`force-postfix-unused-binding`). `pick(42, force (1 / 0))` (`pick(a, b) = a`) → error (`force-prefix-unused-arg`). Contrast: `pick(42, 1 / 0)` → `42` | CLI (corpus), source: `isForceDemand` / argument handling in `CallExpr` |
| E7 | Prefix `force` forces only the immediately following term | `c = force 50 + 60` is `(force 50) + 60`, giving `110` | CLI (`force-basic`), `lesdump` (AST-001) |
| E8 | The only difference between an ordinary lazy binding and an explicit force is "when it is evaluated." The resulting value is the same | `a = (10 + 20)!` and `b = (10 + 20)` are both `30` | CLI (`force-basic`) |
| E9 | **Thunks are shared and memoized**: no matter how many times the same thunk is demanded, its side effect happens once | With `def g(): Int: print "side;"; 1`: `x = g()`⏎`print "before;"`⏎`print x`⏎`print x` → `before;side;11` | CLI (also consistent with the source of `Force`, where a thunk stores its result) |
| E10 | Arguments are passed as unevaluated thunks (by need) and are **shared** between the parameter and the caller. An argument's side effect happens once | `twice(a) = a + a` with `twice(g())` → `side;2` | CLI |
| E11 | If an argument is a literal, it is an evaluated value; if an identifier, **the existing binding itself** (no new thunk is created); if a force, the forced result; otherwise an unevaluated thunk | `n = 1 / 0`⏎`f(n)` (body `1`) → `1`, no error | CLI (`t31`), source: `CallExpr` / `newCapturedThunk`. Corpus: `ident-arg-not-forced` (not forced at call time), `ident-arg-shares-cell` (the result forced in the callee is shared with the caller's binding: `side;21`) |
| E12 | Evaluating a call (`def`): regardless of the caller, create a child scope of **the scope at definition time (the live one)**, bind the parameters, and run the body. The body's statements are **all executed in order**, and its value is **the value of the last expression statement** (the empty tuple if there is none). Within these 9 nodes, the return value is **always evaluated** (a statement consisting of a single identifier forces: E22; other expressions become values immediately). In the source, `evalExpr(Identifier)` can return an unevaluated thunk, but this is not observable within this scope | `v = id(1 / 0)` does not error at the call (the binding is lazy, so the call itself is not executed). `x = 2` inside a function is a local binding and the outer `x` does not change (`x = 1`, `def f(): Int: x = 2; x`, `print f(), ";", x` → `2;1`). All statements of the body run and the value is the last expression statement (a body of `print "a;"`, `2`, `print "b;"`, `3` → `a;b;3`) | CLI, source: `invokeClosure` / `evalBlock`. Corpus: `call-local-rebind`, `call-body-last-value` |
| E13 | A function body's scope **keeps referring** to the global scope at definition time. Later rebindings are visible | `y = 3`⏎`def f(): Int: y`⏎`print f(), ";"`⏎`y = 4`⏎`print f()` → `3;4` (a snapshot at definition time would give `3;3`) | CLI (`t19`), corpus: `live-global-in-function` |
| E14 | A thunk **snapshots the bindings visible at the time it is created** (copying only the names it refers to; since values are immutable, copying references suffices). Rebindings after creation are not visible from that thunk | `a = 1`⏎`b = a + 1`⏎`a = 10`⏎`print b` → `2` | CLI, source: `captureEnv` in `capture.go` |
| E15 | Names **not included in the snapshot** (unbound at creation time) are looked up in the scope **at evaluation time**. Forward references work, and the latest binding at evaluation time is seen | `b = a + 1`⏎`a = 5`⏎`print b` → `6`. `b = a + 1`⏎`a = 5`⏎`a = 7`⏎`print b` → `8` | CLI (`t6`, `t18`), source: "unbound names are left to the parent" in `captureEnv` |
| E16 | Demanding a thunk again while it is being evaluated is a **blackhole**: runtime error `blackhole: circular reference detected in lazy thunk` (no position information), exit 1. Output up to that point is kept | `x = x + 1`⏎`print "ok"`⏎`print x` → stdout `ok`, stderr `Runtime Error: blackhole: …` | CLI (`t5`), source: `Force` |
| E17 | Arithmetic `+ - * /` (Int) **forces both operands left to right** before computing. Int is arbitrary precision (`big.Int` in Go) | `print 1, g()` gives `g;11` (the side effect of `g` comes before the output of `print`) | CLI, source: `BinaryExpr` in `evalExpr`. Corpus: `order-binary-operands` (arithmetic), `order-print-args` (`print` forces all arguments from the left before writing), `order-binary-abort` (if the left fails, the right is not evaluated) |
| E18 | `n / 0` is `division by zero`. `7 / 2 = 3` | `print 7 / 2` → `3` | CLI |
| E19 | `print` **forces all arguments left to right**, concatenates them, writes them **without a trailing newline**, and flushes immediately. Its value is the empty tuple | `print "a"`⏎`print 1 / 0` → stdout `a` **is kept**, exit 1 | CLI, source: `print` in `registerBuiltins` (calls `Flush`) |
| E20 | `exit(n)` forces its argument and uses it as the exit code (`Int` / `Bool`). It terminates **when demanded** (binding alone does not terminate). Output up to that point is kept | `x = exit(7)`⏎`print "a"`⏎`print x` → stdout `a`, exit 7 | CLI, source: `ExitError` |
| E21 | **Error positions**: a runtime error message is `<file>:<line>: <message> at col <column>`. The position is **that of the innermost thunk (the expression being `Force`d) being forced when the error occurred**, or, if there is no such expression, **the start of the enclosing statement**. The position of a binary expression is that of its operator | `print 5 + (1 / 0)` → col 14 (`/`). A bare statement `1 / 0` → col 1 (start of statement). A bare `1 / 0` in a function body → `:2:` col 5 (start of statement) | CLI (`t27`–`t30`, 4 corpus cases), source: `FormatRuntimeError` and `Force` |
| E22 | **An expression statement consisting of a single identifier forces the variable.** If the value is a function (`def` / builtin), it is **called with 0 arguments**. Otherwise the forced value is the statement's value | `n = 1 / 0`⏎`n`⏎`print "ok"` → exit 1, `:1: division by zero at col 7` (the position of `n`'s thunk). `def hello(): Int: print "hi;"; 1`⏎`hello`⏎`print "end"` → `hi;end` | CLI (corpus: `ident-stmt-forces`, `ident-stmt-calls-function`), source: `ExprStmt` in `evalStmt` (`Force` via `isCallableTarget`). Zero-argument calls of builtins (e.g. a statement of just `print`) not observed |

**Observational limits of E2 and E12 (additional verification in P1c-3)**: The effect of E2 (referencing a variable as an expression does not force it) appears only when the reference occurs in a lazy position (the right-hand side of a binding, an identifier argument), and the result there is already given by E1 (the right-hand side is deferred) and E11 (an identifier argument is the existing binding). In strict positions (arithmetic, arguments of `print`), the consumer forces, so it cannot be distinguished from an implementation where "referencing forces." We therefore **do not claim to have demonstrated E2 as an independent rule** (`alias-binding-not-forced` is a combined check of E1 and E2). The only exception is an expression statement consisting of a single identifier, which forces (E22). For the same reason, E12's "may return an unevaluated thunk" is not observable within the 9 nodes: if a function's last expression statement is an identifier it is forced by E22, and other expressions (arithmetic, calls, literals, `force`) become values immediately, so the return value is always evaluated. There is no example within this scope that distinguishes a deferred return value.

### 2.2 Undetermined (not handled / provisional in this design)

- The behavior when an expression statement consisting of a single identifier is a **builtin** (a zero-argument call of `print` / `exit`) is unobserved. The zero-argument call and forcing of a `def` are confirmed as E22. In the first implementation, a zero-argument call of a builtin explicitly becomes `Halt.error "unsupported"`.
- Rounding of negative numbers in Int `/`, exceptions other than overflow, and type-dependent operations such as applying `+` to String: unobserved. The implementation supports only Int×Int, and everything else is `Halt.error "unsupported"`.
- `referencedNames` (the names put into a snapshot) is an **over-approximation** in Go (it also includes, e.g., names bound by nested lambdas). No example has been found where this makes an observable difference. In Lean, any over-approximation of the free variables is acceptable, and the details are not made to match.
- Places where type information (`InferredType`) affects evaluation results (such as the `Show` check in `print`) are assumed not to occur once type-checked. Within the 9 nodes and the golden files they do not affect results, but in general this is **unverified**.
- Stack depth (the limit of Go's recursion), concurrency, `Producer` thunks (I/O), and all other nodes are out of scope.

## 3. Data types (Lean sketch)

No implementation is placed in `lean/` yet. We only checked that the types below compile with Lean 4.25.0 in a temporary file (consistency of the type definitions). Signatures of `opaque`s are omitted.

```lean
namespace Les.Eval
abbrev Addr := Nat          -- cell number
abbrev ScopeId := Nat       -- scope number

inductive Builtin where | print | exit

inductive Value where
  | int (i : Int)
  | str (s : String)
  | unit                                   -- empty tuple (value of print, value of a body with only bindings)
  | builtin (b : Builtin)
  | closure (params : List Param) (body : List Stmt) (scope : ScopeId)  -- def. scope is the "live" scope at definition time

/-- A thunk's environment. snap is looked up first; otherwise the "current" contents of scope (E14, E15). -/
structure Env where
  snap : List (String × Addr)
  scope : ScopeId

inductive Cell where
  | done (v : Value)                       -- evaluated (literal, forced thunk, builtin, closure)
  | suspended (e : Expr) (env : Env)       -- unevaluated thunk
  | blackhole (e : Expr)                   -- under evaluation (error on re-demand: E16)

structure Scope where
  vars : List (String × Addr)              -- "current" bindings; replaced on rebinding (E3)
  parent : Option ScopeId                  -- the root holds the builtins (print, exit)

structure Heap where
  cells : Array Cell
  scopes : Array Scope

/-- State of an error's position. Distinguishes "awaiting a position" from "deliberately no position" (E16, E21). -/
inductive ErrPos where
  | pending                                -- no position yet; the innermost demand / whnf / exec attaches one exactly once
  | absent                                 -- deliberately has no position (blackhole); nothing is attached
  | at (p : Pos)                           -- already attached; not overwritten

inductive Halt where
  | exit (code : Int)                      -- E20
  | error (msg : String) (pos : ErrPos)
  | outOfFuel                              -- no counterpart in Go; "inconclusive" in differential tests

structure Machine where
  heap : Heap
  stdout : String                          -- output accumulates here and survives a `Halt` (E19, E20)

/-- **ExceptT on the outside, state on the inside.** Throwing a `Halt` does not lose the `Machine` (stdout and Heap),
    and the result is `(Except Halt α, Machine)`, returning the final state on both success and failure.
    With the reverse order `StateT Machine (Except Halt)` the state is discarded when throwing, and E19 / E20 cannot be produced. -/
abbrev EvalM := ExceptT Halt (StateM Machine)

structure Outcome where
  stdout : String
  halt : Option Halt                       -- none = normal termination
end Les.Eval
```

Signatures (to be written at implementation time; only names and types here):

```lean
-- evalE   : Nat → Expr → Env → EvalM Addr          evaluate an expression and return a cell (may remain a thunk: E2)
-- whnf    : Nat → Addr → EvalM Value                force a cell into a value (Go's Force: sharing, memoization, blackhole)
-- demand  : Nat → Expr → Env → EvalM Value          = evalE then whnf (Go's Force(NewThunk(e, env)))
-- exec    : Nat → Stmt → ScopeId → EvalM (Option Addr)   execute a statement; only ExprStmt returns a value (E12)
-- run     : Nat → CheckedProgram → Outcome
```

Key points of the design:

- **A name always points to a cell.** Names do not hold a `Value` directly; whether something is evaluated is held by the `Cell`. Sharing the same `Addr` gives sharing and memoization (E9, E10).
- **Scopes live in the Heap.** Go's `Environment.store` is mutable, and rebinding overwrites the same `store`. We represent this as updates to `Scope.vars`. A thunk's `Env` has two layers, `snap` (a copy of the bindings at creation time) and `scope` (the live scope), so that E14 (rebindings after creation are not visible) and E15 (names that were unbound see the latest binding at evaluation time) hold simultaneously. A purely persistent environment alone cannot produce both (in the `a = 7` example of E15 it would give 6 instead of 8).
- `Value.closure.scope` is also a `ScopeId` (the live scope), satisfying E13.

## 4. Evaluation procedure

Termination is ensured by **making fuel an argument of structural recursion** (Lean functions are not made `partial`). `evalE` / `whnf` / `exec` `throw Halt.outOfFuel` if fuel is 0; otherwise fuel is `n+1` and `n` is passed to recursive calls.

- Fuel bounds the **nesting depth of calls**, not the total number of steps. Non-termination arises only from recursion (a `def` calling itself) or circular references, and both increase depth. Circular references are detected by the E16 blackhole, so they do not use fuel.
- Pathological programs whose total number of steps grows exponentially cannot be contained by fuel alone. The first implementation handles only the small golden programs, so this is acceptable; if it becomes a problem, a step budget will be added to the state.
- `outOfFuel` is treated as "inconclusive" in comparisons with Go, counted as neither PASS nor FAIL.

### 4.1 Expressions

| Node | Procedure |
|---|---|
| `Int` / `String` | Allocate a new evaluated cell (`done`) (E11) |
| `Ident n` | Look up `snap`, otherwise the current binding in `scope`. **Do not force.** If not found, `Halt.error "undefined identifier: n"` (unreachable if type-checked) |
| `Binary op l r` (`+ - * /`) | `demand l`, then `demand r` (E17). If both are `Int`, compute and return a `done` cell. For `/` with right operand 0, `division by zero`. Other types are `unsupported` (2.2) |
| `Force e` | Perform `demand e env` **now** and return the result in a `done` cell (E6) |
| `Call f args` | Get the callee's value with `demand f`. Then prepare arguments **from the left**: `Int`/`String` literal → `done`; `Ident` → the existing cell (E11); `Force` → `done` of the `demand`ed value; otherwise → `suspended a (capture a scope)` (E10, E11) |
| Callee is `builtin print` | `whnf` all arguments from the left (E19), concatenate `Int` and `String` and append to `stdout`. Returns `unit`. Other types are `unsupported` |
| Callee is `builtin exit` | With 0 arguments 0; with 1 argument, `whnf` it and use the `Int` (or Bool) as the exit code, `Halt.exit` (E20) |
| Callee is a `closure` | Create a child scope under `closure.scope`, bind parameter names to the argument cells (`unit` if arguments are missing), and run the body with `execBlock` (E12) |

`capture e scope`: put into `snap` only those free variable names of `e` (an over-approximation is fine: 2.2) that are **currently found along the `scope` chain**. Names not found are not included (E15). However, if `e` is `Ident n` and `n` is bound, reuse the existing cell rather than creating a new one (E11).

### 4.2 Forcing: `whnf`

`whnf a` does case analysis on the cell.

- `done v` → `v`.
- `suspended e env` → rewrite the cell to `blackhole e`, perform `demand e env` (following with `whnf` if the result is another cell), and rewrite the cell to `done v` with the obtained value (**memoization**: E9. Go also releases `Thunk.Env`).
- `blackhole _` → `Halt.error "blackhole: circular reference detected in lazy thunk" ErrPos.absent` (E16. **It deliberately has no position**, so no subsequent layer attaches one).

Error positions (E21): primitive errors such as arithmetic errors (`division by zero`) and `unsupported` are thrown with `ErrPos.pending`. When `whnf` / `demand` receive a `pending` error, they **attach the position of their expression, making it `at`**. `exec` **attaches the statement's position** to an error that has propagated up to the statement still `pending`. **`at` and `absent` are not changed** (corresponding to Go's `FormatRuntimeError` not reformatting an already formatted message). The position of a `Binary` is the `pos` from `lesdump` (the operator position) as is. Invariant: no `pending` error remains when `run` returns (since the outermost `exec` always attaches one). The blackhole is thrown with `absent`, so no position is attached.

### 4.3 Statements

- `VarDecl n _ rhs` (in `scope`):
  1. **`n` is already among the current bindings of `scope` (rebinding)**: `demand rhs` (no snapshot; not needed since evaluation happens now) → rebind `n` to `done v` (E3, E4).
  2. Otherwise, if `rhs` is an `Int`/`String` literal: bind `done` (same as Go; observationally indistinguishable).
  3. Otherwise, if `rhs` is `Force _`: `demand` it and bind `done` (E6).
  4. Otherwise: bind `suspended rhs (capture rhs scope)` (E1).
  Whether it is a rebinding is decided **only in that scope** (parent scopes are not consulted; Go's `env.store`). `x = ...` to a name that exists only in a parent creates a new local binding and leaves the parent unchanged (confirmed (CLI): `x = 1`⏎`def f(): Int: x = 2; x`⏎`print f(), ";", x` → `2;1`).
- `FuncDef n params ret body`: bind `done (closure params body scope)`. Type annotations are ignored (section 1).
- `ExprStmt (Ident n)` (E22): get the cell with `evalE` and **force it with `whnf`** (errors surface here). If the value is a `closure`, call it with 0 arguments and use the result as the statement's value. Otherwise (`int` / `str` / `unit`) the forced cell is the statement's value. Zero-argument calls of builtins are unsupported (2.2).
- `ExprStmt e` (`e` not an identifier): the cell from `evalE e` is the statement's value.

The value of a block is the cell of the last `ExprStmt` that returned a value; if there is none, `unit` (E12). At top level all statements are executed, stopping when a `Halt` occurs.

### 4.4 Expected results under the revised design (3 cases)

Since the state is `ExceptT Halt (StateM Machine)`, in every case `Machine.stdout` at the moment of the `Halt` becomes `Outcome.stdout`.

The results of the 3 cases below were confirmed by running, with Lean 4.25.0, a toy model (not the evaluator, and not kept in the repository) that minimally mirrors `ErrPos`, `Halt`, `EvalM`, and the layer that "attaches positions only to `pending`," and checking that it produces the outputs in the comparison format written below.

**(1) `exit-status`** (`print "ok"`⏎`exit(7)`)
1. Statement 1: `print` appends `"ok"` to `Machine.stdout` (`stdout = "ok"`).
2. Statement 2: evaluate `exit` as the callee, force argument `7`, and throw `Halt.exit 7`. The state remains in the outer `StateM`.
3. `Outcome = { stdout := "ok", halt := some (.exit 7) }` → comparison format `{"stdout":"ok","stderr":"","exit_code":7}`. Matches `exit-status.expect.json` (with the stacking order before the fix, `stdout` would be empty and it would not match).

**(2) Runtime error after output** (`print "a"`⏎`print 1 / 0`; CLI observation is E19)
1. Statement 1: `stdout = "a"`.
2. Statement 2: `print` applies `whnf` to the argument thunk (`1 / 0`, position of `/` at line 2, column 9). `demand` forces `1` and `0`, and `/` throws `Halt.error "division by zero" .pending`.
3. That thunk's `whnf` / `demand` receives `pending` and attaches the expression's position, making it `.at (2, 9)`. The upper layer (`exec`) sees `at` and does not change it.
4. `Outcome = { stdout := "a", halt := some (.error "division by zero" (.at ⟨2, 9⟩)) }` → `{"stdout":"a","stderr":"Runtime Error: <CASE>:2: division by zero at col 9\n","exit_code":1}`. Matches the Go observation (stdout `a`, `:2: division by zero at col 9`, exit 1).

**(3) Blackhole** (`x = x + 1`⏎`print "ok"`⏎`print x`; CLI observation is E16)
1. Statement 1: `x` is unbound in `scope`, so it does not go into `snap`, and the cell `c` of `suspended (x + 1)` is bound to `x` (E1, E15).
2. Statement 2: `stdout = "ok"`.
3. Statement 3: `print` applies `whnf` to `c`. It sets `c` to `blackhole` and `demand`s `x + 1`. Looking up the left `x` finds the current binding `c` in `scope`, and `whnf c` hits `blackhole`, throwing `Halt.error "blackhole: circular reference detected in lazy thunk" .absent`.
4. The upper layers (`whnf` / `demand` / `exec`) see `absent` and **do not attach a position**.
5. `Outcome = { stdout := "ok", halt := some (.error "blackhole: …" .absent) }` → `{"stdout":"ok","stderr":"Runtime Error: blackhole: circular reference detected in lazy thunk\n","exit_code":1}`. Matches the Go observation (stdout `ok`, no position, exit 1).
- Note: in this example the variable has no type annotation, so Go prints a `Type Warning` to stderr (observed in `t5`). When adding it to the corpus, a way of writing it without the warning needs to be found (unconfirmed).

## 5. Comparison format between the Go CLI and Lean

Aligned with the same shape as `difftest/corpus/*.expect.json`. Both the Go side (observations from `run.py`) and the Lean side (results of `run`) produce **one common normalized form**, and `stdout` / `exit_code` / `stderr` are compared exactly.

```json
{ "stdout": "30 70 110", "stderr": "", "exit_code": 0 }
```

- `Halt.exit c` → `exit_code = c`, `stderr = ""`. `halt = none` → `exit_code = 0`.
- `Halt.error msg (.at pos)` → `exit_code = 1`, `stderr = "Runtime Error: <CASE>:<line>: <msg> at col <col>\n"` (`<CASE>` is the same placeholder `run.py` substitutes for the case path). `Halt.error msg .absent` (blackhole) → `stderr = "Runtime Error: <msg>\n"`. `.pending` never comes out of `run` (the invariant in 4.2). `stdout` is `Machine.stdout`, always emitted regardless of the kind of `Halt`.
- Go's `Type Warning` goes to stderr, so golden expectations are limited to **type-annotated** programs (no warnings), same as the P0 policy.
- `outOfFuel` is excluded from comparison (counted separately as "inconclusive").
- The Lean executable reads the `lesdump` JSON and prints the JSON above to standard output. The plan is to compare by adding a "match Lean output against Go observations" mode to the existing `difftest/run.py` (implementation is the next task).

## 6. Implementation order for the 10 golden cases

All 10 cases are within the 9 nodes and type-annotated (no warnings). However, they need different mechanisms, so they are split into two stages.

**Stage A (first implementation target; no closures; 7 cases)**: one scope (global); `Cell` / `whnf` / `capture` / `print` / `exit` suffice.

| Case | Rules used |
|---|---|
| `basic-print` | E1, E17, E19 |
| `print-no-newline` | E19 |
| `exit-status` | E19, E20 |
| `div-zero-control` | E18, E21 |
| `lazy-unused-binding` | E1 |
| `force-postfix-unused-binding` | E6, E21 |
| `force-basic` | E6, E7, E8 |

**Stage B (next target; `def` and calls; 3 cases)**: needs `Value.closure`, sharing of argument cells (E10, E11), and child scopes (E12).

| Case | Rules used |
|---|---|
| `lazy-unused` | E10, E12, E22 |
| `force-postfix-unused-arg` | E6, E10, E21, E22 |
| `force-prefix-unused-arg` | E6, E10, E21, E22 |

**Rules not in the golden files (Stage C)**: rebinding (E3–E5), snapshots and forward references (E14, E15), memoization and sharing (E9, E10), blackhole (E16), global references from function bodies (E13), deferral of `exit` (E20), and the general rule for error positions (E21) are **barely verified** by the current golden files. Add the minimal reproductions from 2.1 to `difftest/corpus/` with type annotations (they fit within the 9 nodes of `lesdump`). **E3–E5, E9, E10, E14–E16, and E19–E21 were added in P1c-3 as 12 cases, and E11–E13, E17, and E22 (plus the combined check of E1 and E2) as 11 more cases in the same PR** (see the mapping table in `difftest/corpus/README.md`). **E18's "`n / 0` is division by zero" is verified by the existing `div-zero-control`.** What is not in the corpus: E18's `7 / 2 = 3` (the value of Int division), rounding of negative numbers, and an independent check of E2 (indistinguishable, as noted above). Without these additions, comparison with Go cannot tell whether the core of this design (Heap, scopes, snap) is correct.

## 7. Design decisions and their rationale

| Decision | Adopted | Reason / rejected alternatives |
|---|---|---|
| Representation of environments | A thunk's `Env` has two layers: `snap` + live `scope` | The same observations as Go's `captureEnv` (E14, E15) are needed. A persistent environment alone cannot produce E15's "latest binding at evaluation time," and a mutable scope alone cannot produce E14 |
| What names point to | Always an `Addr` (cell) | Sharing and memoization (E9, E10) can be expressed by identity of `Addr`. Holding a `Value` directly cannot express sharing |
| Rebinding | Evaluate the right-hand side immediately and replace with `done` | Go's behavior (E3). Deferring it would create circular references (consistent with the reason in the source comment) |
| Termination | Fuel as an argument of structural recursion; not `partial` | Does not hinder later proofs (termination, soundness of laziness). The cost is that the total number of steps cannot be bounded (section 4) |
| Output | Accumulate in `Machine.stdout`; keep it on errors and exit | E19, E20. Goes directly into `stdout` of the comparison format (section 5) |
| Error positions | Three states of `ErrPos` (`pending` / `absent` / `at`). Only `pending` is turned into `at`, exactly once, by `whnf` / `demand` / `exec` | Besides the same idempotence as Go's `FormatRuntimeError` (does nothing if the message already contains ` at col `), this distinguishes errors that **deliberately have no position**, like the blackhole (an unformatted panic in Go). With `Option Pos`, "awaiting a position" and "no position" cannot be distinguished (pointed out in a Codex review) |
| Monad stacking order | `ExceptT Halt (StateM Machine)` | To keep the `Machine` (stdout) when a `Halt` is thrown. With `StateT Machine (Except Halt)` the state is discarded, and output before `exit` or an error cannot be produced (pointed out in a Codex review; confirmed by throwing the equivalent of `exit` in Lean) |
| Types | The evaluator does not read them | Section 1. Stay at the boundary of trusting Go's type check results, and make no type-safety claims on the Lean side |

`semantics-opus` was not consulted. The point where multiple reasonable candidates diverged (representation of environments) was uniquely determined by Go observations (E14, E15).

**Differences in P1c-4**: The implementation added `Halt.unsupported (what : String)` (to distinguish hitting a mechanism Stage A does not handle from an `error`; in comparisons it counts as UNSUPPORTED, not PASS). User globals are placed in a child scope (1) of the builtin scope (0).

## 8. Candidate next tasks

1. Add E3–E5, E9–E10, E14–E16, E20, and E21 from the minimal reproductions in 2.1 to the corpus with type annotations, and create `lesdump` golden files (within the 9 nodes; Go observations only, no Lean implementation needed yet).
2. Then implement the Stage A evaluator.
