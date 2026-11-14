# 規則の台帳

状態: `仮説` / `Go CLI 観測済み` / `Lean 比較済み` / `未解決`。
**固定 SHA:** `upstream/LES_COMMIT` を参照。テスト一つで一般化しない。

| ID | 対象・仮説 | 状態 | 根拠 | 次の確認 |
|---|---|---|---|---|
| LZ-001 | 未使用の関数引数は評価されない（少なくとも `choose(42, 1 / 0)`） | 仮説 | upstream `pkg/eval/eval_test.go` の `TestMVP3_LazyUnusedArguments` | 固定コミットの CLI で `difftest/corpus/lazy-unused.les` を実行 |
| LZ-002 | `force` / postfix `!` は要求時評価の境界になる | 仮説 | 同ファイルの `TestForceBuiltinAndPostfixOperator` | CLI で最小反例を独立検証 |
| LZ-003 | Thunk は評価結果をメモ化し、循環する強制評価を検出する | 仮説 | upstream `pkg/eval/value.go` の `Thunk` / `Force` | 作用の回数・循環例を設計 |
| IO-001 | `print` は自動改行せず、引数を評価して出力する | 仮説 | upstream `pkg/eval/eval.go` の `registerBuiltins` | CLI の stdout バイト列で確認 |

更新する際は対象文法・入力例・観測結果・CLI と直接評価器の区別・ソース行/関数・不明点を残す。根拠のない「仕様確定」は禁止。
