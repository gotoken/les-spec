# P2a 実行結果（Heap の基本性質の形式的証明）

- 日時 / upstream SHA: 2026-11-15 (UTC) / `aa78fdcfc76b156e6b5ab4735516fcefadce954b`（Go 側は使っていない）
- 環境: Lean 4.25.0 / Lake 5.0.0。前提: PR #9 を main にマージ済み（`9dcb9ce`。Codex は `672de92` を指摘なしで完了）。P1 の実装・観測フェーズ（P1a〜P1c-6）はこれで完了。
- 追加: `lean/Les/Proofs/Heap.lean`（`Les.lean` から import）。評価器・`Heap` の定義は**変更していない**（`lean/Les/Eval/*` は無変更）。

## 証明した命題（既存の `Heap.alloc` / `Heap.setCell` / `Heap.bind` そのものが対象）

有効なアドレス: `Heap.ValidAddr h a := a < h.cells.size`。

| # | 定理 | 仮定 | 内容 |
|---|---|---|---|
| 1 | `Heap.alloc_cell?_of_valid` | `h.ValidAddr a` | `(h.alloc c).1.cell? a = h.cell? a`（既存アドレスの Cell は不変） |
| 1 | `Heap.alloc_cell?_new` | なし | 新しいアドレス（`alloc_addr`: 古い `cells.size`）には `c` が入る |
| 1 | `Heap.alloc_validAddr` / `alloc_scopes` | `h.ValidAddr a` / なし | 有効なアドレスは保たれる、Scope は不変 |
| 2 | `Heap.setCell_cell?_ne` | `a ≠ b` | `(h.setCell a c).cell? b = h.cell? b` |
| 2 | `Heap.setCell_cell?_self` | `h.ValidAddr a` | 更新したアドレスは `some c` |
| 2 | `Heap.setCell_size` / `setCell_validAddr` / `setCell_scopes` | なし / `h.ValidAddr b` / なし | 個数・有効アドレス・Scope は不変 |
| 3 | `Heap.bind_cells` | なし | `(h.bind s n a).cells = h.cells`（Cell の配列そのものが不変） |
| 3 | `Heap.bind_cell?` / `bind_validAddr` / `bind_scopes_size` | なし / `h.ValidAddr b` / なし | どのアドレスの Cell も不変、有効アドレス・Scope の個数も不変 |
| 3 | `Heap.bind_lookupLocal_self` | `s < h.scopes.size` | `bind` 後にその名前は `a` を指す（`bind` が名前の対応を変える操作であることの確認。追加・置き換えの 2 通り） |

## 命題の形について

- 指示の 2「更新対象と異なる**有効**アドレス」: `setCell_cell?_ne` は `b` の有効性を**仮定しなくても**成り立つ（範囲外の `set!` は何もしない）ので、より強い形で示した。有効性が要るのは `setCell_cell?_self`（更新が実際に起きる条件）と有効アドレスの保存だけ。
- `alloc_cell?_of_valid` の有効性は**必要**: 最小反例は `a = h.cells.size`（`h.cell? a = none` だが `alloc` 後は `some c`）。`alloc_cell?_new` がその場合の正しい形。
- 指示の 3 は `bind_cells`（等式）で示し、そこから `bind_cell?` が従う。

## 未証明の性質（P2b 以降の対象。今回は扱っていない）

- `bind` が他の名前・他のスコープの対応を変えないこと、`lookup` / `lookupFrom`（親をたどる探索）の性質。
- `Heap.initial` の整合性（全束縛が有効なアドレスを指す、親スコープが有効、など）と、評価器の各ステップでの保存。
- `whnf` のメモ化の健全性、スナップショット（E14, E15）、評価器レベルの性質（`Machine` の不変条件、停止性）。
- `alloc` / `setCell` / `bind` を組み合わせた「Heap の整合性」の述語（`WellFormed`）は定義していない。

## 公理

`#print axioms` の確認: 標準の `propext` / `Classical.choice` / `Quot.sound` のみ（`bind_cells` / `bind_cell?` / `bind_validAddr` は公理なし）。`sorry` / `admit` / 新たな `axiom` は無い（`grep` で確認）。

## 使用したタクティクと試行

`unfold`、`simp` / `simp only`（`Array.getElem?_push`, `Array.set!_eq_setIfInBounds`, `Array.getElem?_setIfInBounds`, `Array.size_push`, `List.find?_cons`, `List.map_cons`）、`split`、`by_cases`、`induction`、`show` / `rw` / `exact`、`generalize`。`omega` は `Addr`（`abbrev Nat`）の目標で使えなかったため `Nat.lt_succ_of_lt` に置き換えた。

試行回数: 全体で 9 回のコンパイル。失敗の内訳と修正: `Array.getElem?_set!` は 4.25 に無く `set!_eq_setIfInBounds` 経由に変更（1 回）、`alloc_validAddr` の `omega` が通らず `Nat.lt_succ_of_lt` に変更（2 回）、`bind_lookupLocal_self` の補助補題 `find_replace` で `simp` が展開しすぎるため `simp only` に変更（2 回）、`if True` の簡約順（1 回）。同じ問題で 3 回を超えたものは無い。

## 検証

`lake build` 成功。既存の回帰: コーパス 35 件 PASS 35 / FAIL 0 / OUT_OF_FUEL 0 / UNSUPPORTED 0、個別テスト 41 件 PASS、`les-syntax-test ../lesdump/golden 35` 通過、`python3 difftest/run.py` 35/35。評価器の意味は変えていない（`partial` / `unsafe` の追加なし）。

## モデル利用

Sonnet 5.5 が進行・実装。`semantics-opus`: 0 回（証明戦略は 3 回以内に定まった）。トークン量は未計測。
