# Corpus

`*.les`: 実行コード、`*.stdin`: 標準入力（任意）、`*.expect.json`: 正確な stdout / stderr / exit_code の期待値。

初期ケースは upstream の Go 実装・Go テストから選んだ **未実行の候補**です。P0 の `run.py` で実際に照合し、不一致があれば期待値を勝手に追認しないで原因を記録してください。今後はケースごとに規則 ID を付けていきます。

## stderr の照合
`run.py` は stderr 中のケースファイルの絶対パスを `<CASE>` に置換してから期待値と比較する。エラー系ケースは `stderr` を期待値に書いて厳密に比較する（exit code が合うだけでは PASS にならない）。
