# Lean の構成（P0 では最小の足場のみ）

後続の予定:

```text
lean/
├── Les/
│   ├── Syntax/      -- AST / JSON（必要になってから）
│   ├── Core/        -- Expr / Value / Env / Heap / Eval
│   ├── Builtins/    -- 組込み・未解釈の外部関数
│   ├── Types/       -- 型に依存する部分
│   └── Thm/         -- 定理（最終段階）
├── IO.lean          -- stdin/stdout/終了コードとの接続
└── Main.lean        -- JSON 入力と実行器（後段）
```

最初のモデルは fuel 付き評価器と観測可能な出力を返す。遅延計算の共有・評価中・評価済みの区別を保持し、言語全体の構文解析器を Lean に複製しない。

`lakefile.toml` / `lean-toolchain` は **実際に使える Lean バージョンを確認してから**作成する。ドキュメントだけで `lake build` 成功と報告しない。

## P0 で確認済みの状態

- `lean-toolchain`: `leanprover/lean4:v4.25.0`、`lakefile.toml` + `Les.lean`（意味論なし）で `lake build` 成功。
- この cloud 環境では `release.lean-lang.org` への接続が拒否されるため `elan toolchain install` は失敗する。GitHub Releases の `lean-4.25.0-linux.tar.zst` を `.work/toolchains/` に展開し、その `bin/` を `PATH` 先頭に置いて `lake build` した。詳細は `tasks/results/P0.md`。

## P1c-1: 構文層（`Les/Syntax/`）

`lesdump` の JSON（schema_version 1）を型付き AST に読み込む。評価器・Thunk・Heap・定理はまだ無い。

- `AST.lean`: `Pos` / `Expr`（6 種）/ `Stmt`（3 種）/ `Param` / `Analysis` / `Program` / `CheckedProgram`。整数は Lean の `Int`、型注釈は未解釈の文字列（空 = 注釈なし）。
- `Decode.lean`: `Lean.Data.Json`（標準ライブラリ）だけを使うデコーダー。未知の `schema_version`・未対応の `kind`・必須フィールド欠落・型違い・不正な JSON は、JSON 上の場所付きの `Except.error`。
- `Encode.lean`: AST を同じ JSON に書き戻す（テスト用。golden の往復一致で構造の保持を確認する）。
- `Program.check`: `analysis.status = ok` のものだけを `CheckedProgram` にする。後の評価器は `CheckedProgram` だけを受け取る設計で、型エラーのプログラムは型の上で評価に渡せない。

```
cd lean && lake build                                   # Les と テスト実行ファイルをビルド
lake exe les-syntax-test ../lesdump/golden 10           # golden 10 件の読込・往復・拒否テスト
```
