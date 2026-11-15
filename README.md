# les-spec

[unak/les](https://github.com/unak/les) の**固定コミットにおける観測可能な振る舞い**から、小さな実行意味論を推定し、Lean で実行可能な評価器と定理を作る実験です。

Go 実装の逐語移植ではありません。Lean モデルについての証明と、Go CLI と Lean 評価器の**有限のテストでの一致**を区別しています。

## 現在の到達点（2026-11-15）

- 対象の Les コミット: [`upstream/LES_COMMIT`](upstream/LES_COMMIT)（`aa78fdcf…`）
- Go のパーサー・型解析を利用した `lesdump` の JSON AST → Lean でデコード → fuel 付き評価器を実行
- 式6種類・文3種類の限定構文について Go / Lean の観測結果 **35件 PASS**、Lean 個別テスト **41件 PASS**（各工程の実行記録による）
- Lean モデルに対する Heap 操作、Thunk のメモ化、環境捕捉と前方参照、構造的 Heap 整合性、Cell 数単調性の証明
- P2d-5 の成功時メモ化統合定理 [PR #19](https://github.com/gotoken/les-spec/pull/19) まで main に反映済み
- [PR #20](https://github.com/gotoken/les-spec/pull/20) で具体例による非空虚性の定理を [`NonVacuity.lean`](lean/Les/Proofs/NonVacuity.lean) に追加（main にマージ済み。初回のビルド失敗は [PR #22](https://github.com/gotoken/les-spec/pull/22) で修正し CI で検証済み）

詳細は **[P0〜P2d-5 の成果と証明範囲](docs/proof-coverage.md)**、進め方を変えた理由と今後の仮の工程は **[PLAN.md](PLAN.md)** を参照してください。

**未証明:** Go と Lean の一般的な意味論的同値性、Go の型推論の正しさ、Les 全体の型安全性、Cell 内部参照を含む完全な Heap 整合性など。

## 検証環境を再現する

必要: `git`、`go`、`python3`、Lean 4.25.0 / Lake（`lean/lean-toolchain` を参照）。

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

`difftest/run.py` は固定 Go CLI の観測期待値を検証し、`les-eval-test` は Lean モデルを同じコーパス期待値と比較します。実行されたテスト数の記録は [P1c-6](tasks/results/P1c-6.md)・[P2d-5（PR #19）](https://github.com/gotoken/les-spec/pull/19) を参照してください。

環境によっては Lean の toolchain の取得が制限されます。初回のセットアップで使用した回避策は [P0](tasks/results/P0.md) と [lean/README.md](lean/README.md) に記録しています。

## リポジトリ案内

- [PLAN.md](PLAN.md): 当初の計画、2026-11-15 の P2 証明優先への変更理由、後続工程の候補
- [docs/proof-coverage.md](docs/proof-coverage.md): P0〜P2d-5 の成果、E1〜E22 の証明対応、定理の依存関係、未証明の範囲
- [docs/evaluator-design.md](docs/evaluator-design.md): Go 観測から整理した評価規則 E1〜E22 と設計
- [ledger/rules.md](ledger/rules.md): Go CLI 観測の根拠付き台帳
- [upstream/LES_COMMIT](upstream/LES_COMMIT): 固定した Go upstream コミット
- [difftest/](difftest/): Go CLI の観測と正規化された期待結果
- [lesdump/](lesdump/): Go のパーサー・型解析を用いた AST JSON 化
- [lean/Les/Eval/](lean/Les/Eval/): Lean 評価器
- [lean/Les/Proofs/](lean/Les/Proofs/): 評価器・Heap の定義に対する Lean の定理。`NonVacuity.lean` は P2d-5 の前提を満たす具体例と統合定理の適用
- [tasks/results/](tasks/results/): 各工程のビルド・テスト・モデル利用・未解決事項の記録
- [CLAUDE.md](CLAUDE.md): AI 作業の基本方針（小さな作業単位、停止条件）
- [tasks/next.md](tasks/next.md): **初期 P0 の指示を残した履歴**。現在の作業指示として再実行しないこと

## 次の作業について

次の言語機能追加・証明対象はまだ確定していません。[成果と証明範囲](docs/proof-coverage.md) と P2d-5 の非空虚性証明をレビューし、PR #22 の修正と CI の検証結果を確認したうえで次のタスクを決めます。

無断で次フェーズに着手せず、一つのタスクごとに実行、検証、記録、レビューを行います。モデル利用量が取れなかった工程は「未計測」とします。
