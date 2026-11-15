# P1a 実行結果

- 日時 / upstream SHA: 2026-11-15 (UTC) / `aa78fdcfc76b156e6b5ab4735516fcefadce954b`（P0 のビルド済み CLI `.work/bin/les` を使用）
- ブランチ: `p1a-force-observation`。PR #1（P0）が未マージだったため、`p0-oracle-lean-scaffold` の上に積んでいる。
- 変更ファイル:
  - `difftest/run.py`: stderr 中のケースファイルの絶対パスを `<CASE>` に置換してから比較
  - `difftest/corpus/div-zero-control.expect.json`: stderr を厳密に期待（`Runtime Error: <CASE>:1: division by zero at col 9`）
  - 追加（LZ-002、いずれも型注釈あり）: `force-basic`, `force-postfix-unused-arg`, `force-prefix-unused-arg`, `lazy-unused-binding`, `force-postfix-unused-binding`（各 `.les` + `.expect.json`）
  - `difftest/corpus/README.md`、`ledger/rules.md`（LZ-002）、`tasks/results/P1a.md`

## 成功したコマンド（終了コード）

| コマンド | exit |
|---|---|
| `python3 difftest/run.py` | 0（10/10 PASS） |
| 変異確認: `div-zero-control` の期待 stderr を `…boom` に書き換えて `run.py` | FAIL stderr を検出（その後元に戻し、再実行で 10/10 PASS） |

## 観測（固定 SHA の CLI、型注釈あり）

| ケース | stdout | stderr | exit |
|---|---|---|---|
| lazy-unused（`pick(42, 1 / 0)`、第 2 引数は未使用） | `42` | 空 | 0 |
| lazy-unused-binding（`x = 1 / 0` を使わない） | `ok` | 空 | 0 |
| force-postfix-unused-arg（`pick(42, (1 / 0)!)`） | 空 | `Runtime Error: <CASE>:4: division by zero at col 19` | 1 |
| force-prefix-unused-arg（`pick(42, force (1 / 0))`） | 空 | `…:4: division by zero at col 25` | 1 |
| force-postfix-unused-binding（`x = (1 / 0)!`） | 空 | `…:1: division by zero at col 8` | 1 |
| force-basic | `30 70 110` | 空 | 0 |

通常の遅延評価（未使用の `1 / 0` は評価されない）と強制評価（`!` / `force` を付けるだけで、使われなくてもその場で評価され失敗する）の差が、引数・束縛の両方で観測できた。エラーの列番号は `/` の位置と一致する。

## 失敗と修正

なし（同じ失敗への修正は 0 回）。upstream のソースは変更していない。

## モデル利用

- 窓口モデル: スレッドは Opus 5.5 で起動し、確認のうえ **Sonnet 5.5 に切り替えてから** P1a を実施した（ユーザーが選択）。この変更のコミットは Sonnet 5.5。
- トークン量: Sonnet・Opus とも **未計測**。
- `semantics-opus` サブエージェント: 0 回。CLI 観測だけで判断できたため。

## 未解決

- `force` の対象がタプル・辞書・メソッド呼出の場合（`eval_test.go` 5–6 節）は未観測。
- `force 50 + 60` が 110 になる優先順位と、`force` のメモ化への影響は、CLI 観測のみでソース読解は未実施。
- PR #1 が未マージなので、この PR は #1 を土台にしている。#1 のマージ後は base を main に付け替える。

## 次の一つのタスク候補

LZ-002 の残り（タプル・辞書への `force`）を CLI で観測する。P1b（lesdump）には進んでいない。
