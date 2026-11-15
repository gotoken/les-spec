# Corpus

`*.les`: 実行コード、`*.stdin`: 標準入力（任意）、`*.expect.json`: 正確な stdout / stderr / exit_code の期待値。

初期ケースは upstream の Go 実装・Go テストから選んだ **未実行の候補**です。P0 の `run.py` で実際に照合し、不一致があれば期待値を勝手に追認しないで原因を記録してください。今後はケースごとに規則 ID を付けていきます。

## stderr の照合
`run.py` は stderr 中のケースファイルの絶対パスを `<CASE>` に置換してから期待値と比較する。エラー系ケースは `stderr` を期待値に書いて厳密に比較する（exit code が合うだけでは PASS にならない）。

## 意味論テストと規則 ID（P1c-3）

`*.expect.json` の `rules` は、`docs/evaluator-design.md` 2.1 節の規則 ID（`run.py` は読まない）。期待値は設計メモの予測を先に書き、固定コミットの Go CLI（オラクル）で照合した。変数宣言は型注釈で `Type Warning` を解消している（解消しても挙動が変わらないことは、注釈なし版を CLI で実行して確認済み: 設計メモの `t5` / `t6` / `t18`）。

| ケース | 規則 ID | 台帳 | 内容 |
|---|---|---|---|
| `rebind-forces-rhs` | E3 | LZ-004 | 再束縛は右辺をその場で強制評価（初回束縛なら遅延） |
| `rebind-old-binding` | E4 | LZ-004 | 再束縛の右辺は古い束縛を参照（`5` → `+1` → `*2` = `12`） |
| `rebind-discards-thunk` | E5 | LZ-004 | 再束縛された古い Thunk は評価されない |
| `snapshot-late-rebind` | E14 | LZ-005 | Thunk は作成時の束縛をスナップショット（後の再束縛は見えない） |
| `forward-ref` | E15 | LZ-005 | 作成時に未束縛だった名前は評価時に引かれる（前方参照） |
| `forward-ref-rebound` | E15 | LZ-005 | 前方参照は評価時の**最新**の束縛を見る（`a = 5` → `a = 7` で `8`） |
| `memo-binding` | E9 | LZ-003 | 束縛された Thunk は共有・メモ化（副作用は 1 回） |
| `arg-sharing` | E10 | LZ-003 | 引数は仮引数と共有（`twice(g())` の副作用は 1 回） |
| `blackhole` | E16 | LZ-003 | 自己参照の Thunk はブラックホール（位置なしのエラー、出力は残る） |
| `exit-lazy` | E20 | EX-001 | `exit` は要求された時に終了、それまでの出力は残る |
| `error-keeps-output` | E19, E21 | EX-001, ER-001 | 実行時エラーでも出力は残る。位置は強制中の Thunk の式 |
| `error-pos-bare-stmt` | E21 | ER-001 | Thunk 外のエラーは文の先頭位置 |

既存 10 件（`basic-print` など）の規則 ID は `tasks/results/P1c-3.md` に対応表がある。
