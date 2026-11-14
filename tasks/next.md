# NEXT — P0: Go オラクルの一周と Lean の足場

**担当:** Claude Code の Sonnet（窓口）。`semantics-opus` は原則呼ばない。
**対象:** `upstream/LES_COMMIT` の固定コミットのみ。
**作業範囲:** `scripts/`、`difftest/`、`lean/`、`ledger/`、`tasks/results/`、再現に必要な文書。

## 手順

1. `bash scripts/bootstrap.sh` を実行し、Go CLI が指定 SHA からビルドされたか検証する。失敗時は原因を限定して修正する。
2. `python3 difftest/run.py` を実行する。サンプルごとの stdout / stderr / exit を確認し、`tasks/results/P0.md` に短い結果を残す。既存の `eval_test.go` と CLI の型推論経路が異なることに注意。
3. `elan` と `lake` が使用可能なら、`lean/` に Lean の最小プロジェクトを作り、toolchain を固定し、空に近い `Les` モジュールの `lake build` を成功させる。利用できなければコマンドと障害を記録し、Lean 自体は推測で生成しない。
4. `ledger/rules.md` の LZ-001 / IO-001 を、**実際に確認できた範囲でのみ**更新する。
5. `tasks/results/P0.md` に終了時の成果、通ったコマンド、変更ファイル、未解決、次タスク候補、モデル利用実測（取れなければ未計測）を書く。

## 制限

- P0 の終点では **止まる**。P1 の意味論実装、AST+型 JSON 出力器、131 テストの一括抽出、型推論移植、証明はまだ行わない。
- 不明な仕様を Opus に問い合わせる前に、CLI 実行と局所ソース確認で絞る。Opus は P0 合計 0〜1 回。
- 失敗した同じ課題の修正は最大 3 試行。作業が拡散したら停止して記録。
- upstream のソースを変更しない。GitHub push や PR 作成はこのタスクではしない。
- CI で無限ループさせず、予算の大きな作業を自動で連鎖させない。

## 完了・停止条件

Go CLI のコミットが一致し、最低 2 件の期待値テストが成功、結果記録が存在する。Lean ビルドの可否も事実として報告する。失敗なら部分成果を保存して止まる。
