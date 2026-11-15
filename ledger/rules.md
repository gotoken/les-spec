# 規則の台帳

状態: `仮説` / `Go CLI 観測済み` / `Lean 比較済み` / `未解決`。
**固定 SHA:** `upstream/LES_COMMIT` を参照。テスト一つで一般化しない。

| ID | 対象・仮説 | 状態 | 根拠 | 次の確認 |
|---|---|---|---|---|
| LZ-001 | 未使用の関数引数は評価されない（少なくとも `choose(42, 1 / 0)`） | Go CLI 観測済み（この 1 形のみ） | 固定 SHA の CLI で `lazy-unused.les`（型注釈なし）と `lazy-unused-typed.les`（`Int` 注釈あり）が stdout `42`・exit 0。対照 `div-zero-control.les`（`print 1 / 0`）は exit 1・`Runtime Error: …division by zero`、つまり `1 / 0` は評価されれば失敗する。直接評価器側の根拠は `pkg/eval/eval_test.go` `TestMVP3_LazyUnusedArguments`。注意: 型注釈なし版は CLI の型推論（`cmd/les/main.go` → `types.Inferencer`）が stderr に `Type Warning` を 3 行出す。eval_test.go はこの経路を通らない | 引数が複数回使われる・別関数に渡される・`let` 束縛される場合。`force`/`!` との関係は LZ-002 |
| LZ-002 | `force` / postfix `!` は要求時評価の境界になる | 仮説 | 同ファイルの `TestForceBuiltinAndPostfixOperator` | CLI で最小反例を独立検証 |
| LZ-003 | Thunk は評価結果をメモ化し、循環する強制評価を検出する | 仮説 | upstream `pkg/eval/value.go` の `Thunk` / `Force` | 作用の回数・循環例を設計 |
| IO-001 | `print` は自動改行せず、引数を評価して出力する | Go CLI 観測済み（文字列・整数・複数引数） | CLI で `print "a"` / `print "b"` / `print 1, 2` の stdout バイト列が `ab12`（改行なし、複数引数は区切りなしで連結）。`basic-print.les` も `30`。ソース: `pkg/eval/eval.go` `registerBuiltins` の `print` は各引数を `Force` → `Show` 確認 → `String()` → `strings.Join(parts, "")` | 0 引数、`Show` 非実装値、他の `print` 系組込み（存在すれば）の改行有無 |

更新する際は対象文法・入力例・観測結果・CLI と直接評価器の区別・ソース行/関数・不明点を残す。根拠のない「仕様確定」は禁止。
