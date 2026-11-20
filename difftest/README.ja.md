# Go オラクル検証

[English](README.md) | 日本語

`difftest/run.py` は固定コミットの Go CLI を実行し、`corpus/*.les` と同名の `*.expect.json` に基づいて stdout と終了コードを比較する。stderr は記録するが、期待値に `stderr` が指定された場合だけ厳密比較する。**Lean の差分テストは未実装**。

```sh
bash scripts/bootstrap.sh
python3 difftest/run.py
# 例: python3 difftest/run.py --timeout 3 --report .work/custom-results.json
```

期待値 JSON:

```json
{"stdout": "30", "exit_code": 0, "stderr": ""}
```

stdin は同名の `*.stdin` があればバイト列で与え、なければ空とする。改行・空白を正規化せず、stdout/stderr は **バイト列の UTF-8 デコード結果を厳密比較**する。バイナリ I/O を扱う段階で表現を拡張する。

結果の全文は `.work/difftest-results.json` に保存する。モデルに渡すのは失敗ケースだけ。タイムアウトは明示的に失敗する。期待値は観測の承認なしに自動更新しない。
