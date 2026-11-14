# les-spec

[unak/les](https://github.com/unak/les) の観測可能な振る舞いから、小さな実行意味論を推定し、Lean で実行可能なモデルと（後段で）定理を作る実験です。

**方針:** 途中で止めても成果を残す。最初の小さな一周で作業量・モデル利用量を測る。証明と広範な型推論は後回し。

## 最初にやること

必要: `git`, `go`, `python3`、Lean に進む段階で `elan`/`lake`、Claude Code（利用する場合）。

```sh
git clone https://github.com/gotoken/les-spec.git
cd les-spec
bash scripts/bootstrap.sh
python3 difftest/run.py
claude --model sonnet
```

Claude Code への最初の入力:

> `CLAUDE.md` と `tasks/next.md` を読んで、P0 を開始してください。Sonnet が進行役です。未確定の意味論が本当に障害になる場合のみ `semantics-opus` サブエージェントを使ってください。完了条件に達したら `tasks/results/` に結果を残し、予算計測の確認地点で停止してください。

**注意:** このリポジトリを配置しただけでは Claude は自動起動しません。最初の `claude` 実行は利用者が行います。作業途中はローカルで完結し、必要なときだけ git commit / push してください。

## ファイルの案内

- [PLAN.md](PLAN.md): 対象、段階、停止条件
- [CLAUDE.md](CLAUDE.md): Sonnet への短い常設指示
- [tasks/next.md](tasks/next.md): 次の具体的なタスク
- [ledger/rules.md](ledger/rules.md): 根拠付きの仕様台帳
- [upstream/LES_COMMIT](upstream/LES_COMMIT): 固定した upstream コミット
- [difftest/](difftest/): Go CLI の観測実験と、将来の Lean 差分比較
- [lesdump/](lesdump/): AST・型情報 JSON 化の後続実装予定地
- [lean/](lean/): Lean の意味論・実装・証明の後続実装予定地

現時点の `difftest/run.py` は **Go CLI の結果を期待値と比較するオラクル検証**です。Lean との同値性をまだ証明・確認したものではありません。
