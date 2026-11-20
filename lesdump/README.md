# lesdump

English | [日本語](README.ja.md)

Calls Go's `pkg/lexer` / `pkg/parser` / `pkg/types` at the pinned commit (`upstream/LES_COMMIT`) and outputs a **minimal AST JSON** to feed into Lean. It has no parser of its own. This is not an official language specification of les; it is a provisional intermediate representation for handling the current `difftest/corpus/`.

```
bash scripts/bootstrap.sh                 # also builds .work/bin/lesdump
.work/bin/lesdump FILE.les > out.json
python3 lesdump/test.py                   # golden comparison, determinism, error cases (--update to refresh golden files)
```

`go.mod` only refers to the pinned checkout via `replace les => ../.work/upstream-les`; the upstream source is not modified.

## Exit status

- exit 0: JSON written to stdout (syntax OK; type errors are recorded in `analysis`, see below)
- exit 2: syntax error or unsupported node. The reason goes to stderr and stdout is empty. **Unsupported nodes are never silently dropped**

## JSON format (`schema_version` = 1)

The output has a fixed (sorted) key order and an indent of 2, producing the same bytes for the same input. File paths are not included in the output. A fixed diagnostic file name `<FILE>` is passed to the parser, so diagnostics are identical regardless of how the file is specified (relative, absolute, short name), and message bodies are not rewritten.

```
Program   { schema_version, kind:"Program", analysis, body:[Stmt] }
analysis  { status:"ok"|"type_error", type_error:string, type_warnings:[string] }
```

`analysis` is the result of the same `Inferencer.InferProgram` as the upstream CLI (`cmd/les/main.go`). Intermediate results of type inference (per-expression types) are not output; this will be extended when evaluation needs it.

Every node has `kind` and `pos:{line,col}` (1-based).

| Statement | Fields |
|---|---|
| `ExprStmt` | `expr` |
| `VarDecl` | `name`, `type_annot` (`""` if absent), `value` |
| `FuncDef` | `name`, `params:[{name,type_annot,pos}]`, `return_type` (`""` if absent), `body:[Stmt]` |

| Expression | Fields |
|---|---|
| `Ident` | `name` |
| `Int` | `value` (int64) |
| `String` | `value` |
| `Binary` | `op`, `left`, `right` |
| `Force` | `expr` (both prefix `force` and postfix `!` produce this node) |
| `Call` | `callee`, `args:[Expr]` |

`print` / `exit` appear as builtin calls, `Call` + `Ident` (there is no special node).

## Unsupported (explicit error)

All AST nodes not in the tables above (`IfStmt`, `FloatLit`, `UnaryExpr`, structs, `match`, `import`/`module`, etc.), `FuncDef`s with type parameters, `&block` parameters, default values, or variadic parameters, `Call`s with a trailing block, and integer literals beyond int64. Only what becomes necessary as the corpus grows will be added. `CallExpr.WrappedInParens` (a syntactic hint of whether the call was parenthesized) is not output.
