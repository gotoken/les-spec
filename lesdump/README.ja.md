# lesdump

[English](README.md) | 日本語

固定コミット（`upstream/LES_COMMIT`）の Go の `pkg/lexer` / `pkg/parser` / `pkg/types` を呼び出し、Lean に入力する**最小の AST JSON** を出力する。パーサーは独自実装していない。これは les の正式な言語仕様ではなく、現在の `difftest/corpus/` を扱うための暫定的な中間表現である。

```
bash scripts/bootstrap.sh                 # .work/bin/lesdump も作られる
.work/bin/lesdump FILE.les > out.json
python3 lesdump/test.py                   # golden 比較・決定性・エラー系（--update で golden 更新）
```

`go.mod` は `replace les => ../.work/upstream-les` で固定チェックアウトを参照するだけで、upstream のソースは変更しない。

## 終了状態

- exit 0: JSON を stdout に出力（構文 OK。型エラーは `analysis` に記録、後述）
- exit 2: 構文エラー、または未対応ノード。stderr に理由を出し、stdout は空。**未対応ノードを黙って省略しない**

## JSON 形式（`schema_version` = 1）

出力はキー順が固定（ソート済み）・インデント 2 で、同じ入力から同じバイト列になる。ファイルパスは出力に含めない。パーサーに固定の診断用ファイル名 `<FILE>` を渡すので、診断文は指定方法（相対・絶対・短い名前）に依らず同一で、メッセージ本文は書き換えない。

```
Program   { schema_version, kind:"Program", analysis, body:[Stmt] }
analysis  { status:"ok"|"type_error", type_error:string, type_warnings:[string] }
```

`analysis` は upstream CLI（`cmd/les/main.go`）と同じ `Inferencer.InferProgram` の結果。型推論の中間結果（式ごとの型）は出力しない。評価に必要になった時点で拡張する。

全ノードは `kind` と `pos:{line,col}`（1 始まり）を持つ。

| 文 | フィールド |
|---|---|
| `ExprStmt` | `expr` |
| `VarDecl` | `name`, `type_annot`（無ければ `""`）, `value` |
| `FuncDef` | `name`, `params:[{name,type_annot,pos}]`, `return_type`（無ければ `""`）, `body:[Stmt]` |

| 式 | フィールド |
|---|---|
| `Ident` | `name` |
| `Int` | `value`（int64） |
| `String` | `value` |
| `Binary` | `op`, `left`, `right` |
| `Force` | `expr`（prefix `force` と postfix `!` の両方がこのノード） |
| `Call` | `callee`, `args:[Expr]` |

`print` / `exit` は組込み関数の呼出として `Call` + `Ident` で表れる（特別なノードは無い）。

## 未対応（明示的エラー）

上の表にない AST ノード全般（`IfStmt`, `FloatLit`, `UnaryExpr`, 構造体, `match`, `import`/`module` 等）、型パラメータ・`&block` 引数・既定値・可変長引数を持つ `FuncDef`、末尾ブロック付き `Call`、int64 を超える整数リテラル。コーパスが増えて必要になったものだけ追加する。`CallExpr.WrappedInParens`（括弧で囲まれたかの構文上のヒント）は出力しない。
