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
