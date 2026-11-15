# P1b 実行結果

- 日時 / upstream SHA: 2026-11-15 (UTC) / `aa78fdcfc76b156e6b5ab4735516fcefadce954b`（`.work/upstream-les` は変更なし。`git status` 空）
- ブランチ: `p1b-lesdump`（PR #2 のマージを確認してから main の上に作成）
- 変更ファイル:
  - 追加 `lesdump/{go.mod,main.go,test.py,README.md}`、`lesdump/golden/*.json`（コーパス 10 件分）
  - 更新 `scripts/bootstrap.sh`（`.work/bin/lesdump` もビルド）、`ledger/rules.md`（AST-001 を追加）、`tasks/results/P1b.md`

## 実装の要点

- upstream の `pkg/lexer` / `pkg/parser` / `pkg/types` を `replace les => ../.work/upstream-les` で再利用（パーサーは独自実装していない）。CLI と同じ `Inferencer.InferProgram` を通し、結果は `analysis`（`ok` / `type_error` と警告）に入れる。式ごとの型は出力していない。
- 対応ノード: `ExprStmt`, `VarDecl`, `FuncDef`（型パラメータ・`&block`・既定値・可変長なし）, `Ident`, `Int`, `String`, `Binary`, `Force`, `Call`。それ以外は stderr にメッセージを出して exit 2。形式の詳細は `lesdump/README.md`。
- 出力はキー順固定・パスなし（型エラー文中のパスは `<FILE>`）。`schema_version` は 1。

## 成功したコマンド（終了コード）

| コマンド | exit | 結果 |
|---|---|---|
| `go build`（`lesdump/`、`go vet` / `gofmt -l` も問題なし） | 0 | — |
| `python3 lesdump/test.py` | 0 | コーパス 10 件が golden と一致、2 回実行で同一、別パスのコピーでも同一、未対応・構文エラーは exit 2 |
| `python3 difftest/run.py` | 0 | 10/10 PASS |
| `lake build`（`lean/`、P0 と同じ手動ツールチェーン） | 0 | 既存ビルドは壊れていない |

## 観測: `force 50 + 60`

`c = force 50 + 60` は `Binary(+, Force(Int 50), Int 60)`、つまり `(force 50) + 60` に解析される。prefix `force` は直後の項だけに掛かる。`force (1 / 0)` と `(1 / 0)!` は同じ `Force` ノードで、違いは `pos` のみ（prefix はキーワード位置、postfix は `!` の位置）。`ledger/rules.md` の AST-001 に記録した。他の演算子との結合は未観測。

## 型検査経路の確認

型注釈付きの `f("a")` は CLI の `les -t` と同じ型エラー（`expected Int, got String at col 9`）が `analysis.type_error` に出る。`1 + "a"` は CLI でも lesdump でも型エラーにならない（同じ結果）。

## 失敗と修正

- テスト中に 2 回、自分の実装の不備を直した（いずれも 1 回で解消）: (1) 型エラー文に絶対パスが入って決定的でない問題を `<FILE>` 置換で解消、(2) JSON の `<`/`>` が `<` にエスケープされる問題を `SetEscapeHTML(false)` で解消。
- 同じ失敗への修正が 3 回に達したものは無し。upstream のソースは変更していない。

## モデル利用

- 窓口モデル: Sonnet 5.5。トークン量は **未計測**。
- `semantics-opus` サブエージェント: 0 回。

## 未対応構文（意図的）

`IfStmt`, `FloatLit`, `UnaryExpr`, 構造体・`match`・ラムダ・`import`/`module`、型パラメータ等を持つ `FuncDef`、末尾ブロック付き `Call`、int64 超の整数。コーパスに現れないため対応していない。

## 未解決

- `.work/` は gitignore 対象のため、`lesdump` のバイナリはコンテナ内にしか残らない（`bootstrap.sh` で再生成できる）。
- `go.mod` の `replace` が `.work/upstream-les` の存在を前提にしている。事前に `bootstrap.sh` が必要。

## 次の一つのタスク候補

P1c: `lesdump` の JSON を読む Lean 側の `Les.Syntax`（AST 型と JSON デコード）を作り、golden 10 件を読み込めることを確認する。評価器にはまだ進まない。
