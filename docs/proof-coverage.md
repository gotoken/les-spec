# P0〜P2d-5 成果と証明の適用範囲

2026-11-15 時点の中間報告。対象は [`unak/les`](https://github.com/unak/les) の固定コミット `aa78fdcfc76b156e6b5ab4735516fcefadce954b`（[`upstream/LES_COMMIT`](../upstream/LES_COMMIT)）。

**この文書の結論:** Go CLI の観測から9種類の構文ノードに絞った Lean 実行可能評価器を作り、35件のプログラムで stdout・stderr・終了コードを期待値と照合した。さらに、その**Lean モデルについて**、Heap の基本性質、名前解決、Cell 数の非減少性、成功した初回強制のメモ化と再強制の安定性を証明した。**Go 実装と Lean モデルの一般的な同値性は未証明**である。

> **マージ状況:** P0〜P2d-5（[PR #19](https://github.com/gotoken/les-spec/pull/19) を含む）は main にマージ済み（P2d-5 のマージコミット `12e9af9`）。本 PR #20 では P2d-5 の前提を実際に満たす証人を [`lean/Les/Proofs/NonVacuity.lean`](../lean/Les/Proofs/NonVacuity.lean) に追加した。この新規証明は本 PR の変更で、main には未反映。

## 1. 何を作り、どこまで動いたか

| 工程 | 成果物と到達点 | 根拠 |
|---|---|---|
| P0 | Go CLI の対象コミット固定、オラクル5件の実行、Lean 4.25.0 / Lake 5.0.0 の足場 | [P0](../tasks/results/P0.md) |
| P1a | 遅延評価と明示的 `force` / `!` の対照実験。stderr のパス正規化と厳密比較 | [P1a](../tasks/results/P1a.md) |
| P1b | upstream の Go パーサー・型解析を再利用する `lesdump`。JSON AST の固定形式 | [P1b](../tasks/results/P1b.md) |
| P1c-1〜3 | Lean AST/JSON デコーダー、評価器設計、E1〜E22 の観測規則、Go CLI コーパス33件 | [設計メモ](evaluator-design.md)、[P1c-3](../tasks/results/P1c-3.md) |
| P1c-4〜6 | fuel 付き Lean 評価器。`def`、closure、Thunk の共有、環境捕捉を追加し、コーパス35件・個別41件を通過 | [P1c-5](../tasks/results/P1c-5.md)、[P1c-6](../tasks/results/P1c-6.md) |
| P2a〜P2c | Heap 操作・メモ化・環境捕捉と前方参照に関する定理群 | [`lean/Les/Proofs/`](../lean/Les/Proofs/) |
| P2d-1〜4 | 構造的 Heap 整合性、評価器の Cell 数単調性、初回強制後のアドレス有効性の導出 | [P2d-3](../tasks/results/P2d-3.md)、[P2d-4](../tasks/results/P2d-4.md) |
| P2d-5 | 成功した初回強制・メモ化・再強制を1定理へ統合（**PR #19、main マージ済み**） | [PR #19](https://github.com/gotoken/les-spec/pull/19)、[結果記録（PR #19）](https://github.com/gotoken/les-spec/blob/6a7dbc2f651bbc4deaa4be661c86852989f5e6de/tasks/results/P2d-5.md) |

### 実行モデルの範囲

- 入力は Go 側のパーサーと型解析を通った `CheckedProgram`。**型解析の正しさは Lean では証明していない**。
- Lean AST は式6種類（Ident、Int、String、Binary、Force、Call）と文3種類（ExprStmt、VarDecl、FuncDef）。Les 全体の構文ではない。
- `Heap` は Cell と Scope の配列。未評価 `suspended`、評価中 `blackhole`、評価済み `done` を区別し、Cell のアドレスを共有する。
- `Env` は捕捉済みの名前→アドレスを保持する `snap` と、生きた Scope への参照を持つ。捕捉済みの名前は `snap` を優先し、未捕捉名は Scope を検索する。
- `EvalM = ExceptT Halt (StateM Machine)`。例外終了時もそこまでの Heap・stdout の変更が残る。再帰は fuel で制限するが、fuel は総ステップ数の上限ではない。
- 残る未対応機能には Tuple、Dict、`if`、パターン、struct、型推論全体、負数除算の一部などがある。

### テストで確認したことと確認していないこと

- [Go CLI のコーパス](../difftest/corpus/)35件を固定コミットで観測し、Lean 評価器でも同じ期待 stdout・stderr・exit_code へ一致した（報告上、PASS 35 / FAIL 0 / OUT_OF_FUEL 0 / UNSUPPORTED 0）。
- Lean 個別テスト41件、AST のデコード・往復、Go オラクルの差分検査（35/35）が成功したとの [各工程の実行記録](../tasks/results/P1c-6.md) がある。意図的な変更でテストが落ちることも確認した（例: closure の親 Scope、Thunk の `snap`、演算順序）。
- これは**有限のプログラムについての観測的一致**であり、Lean と Go の全入力に対する同値性ではない。GitHub Actions による独立した継続的検証も、この記録からは主張しない。
- `sorry` / `admit` / 新規公理を使わない証明として各 PR にビルド・`#print axioms` の実行記録がある。ただし、文書に記載しただけでは新たな独立検証とはならない。
- AI のトークン量は**未計測**。安価さや人手との優劣について実測比較はない。

## 2. 言語規則 E1〜E22 と形式的保証の境界

凡例：**観測**は固定 Go CLI や `lesdump` の確認、**実行照合**は対応する限定構文で Lean 実行結果を期待値と比較したこと、**直接の定理**は挙動の一部を Lean の全称命題として証明したことを指す。同じ ID に「定理あり」としても、その規則の全側面が証明されたわけではない。元の規則の正確な範囲・再現例は [評価器設計メモ](evaluator-design.md) と [コーパス対応表](../difftest/corpus/README.md) を参照。

| 規則 | 観測・実行照合の対象（部分言語） | Lean の直接の証明と残る境界 |
|---|---|---|
| E1 遅延する初回束縛 | 未使用の `1 / 0` は実行されない | 変数宣言全体の一般定理は未証明 |
| E2 識別子参照は原則強制しない | E1・E11 と組み合わせた観測。**単独規則として識別できていない** | 未証明 |
| E3 再束縛は右辺を即評価 | ゼロ除算の初回束縛との対照 | 再束縛全体の評価タイミングは未証明 |
| E4 再束縛の右辺は古い束縛を参照 | `x = x + 1` など | 未証明 |
| E5 破棄された古い Thunk は不要 | 古い `1 / 0` を使わない | 未証明 |
| E6 `force` / `!` による強制 | 束縛と引数の双方で対照 | 一般的な強制境界は未証明 |
| E7 `force` の結合順序 | Go parser の AST と Lean の JSON 往復で検証 | 構文解析の正しさは未証明 |
| E8 強制の有無と値 | 対応する実行例で比較 | 一般的な値の同一性は未証明 |
| E9 共有 Thunk のメモ化 | 副作用が1回の例など | **証明あり**: `whnf_done`、`whnf_suspended_ok_*`、PR #19 `whnf_suspended_ok_memo`。**成功した demand が前提** |
| E10 引数の call-by-need 共有 | `twice(g())` の副作用が1回 | 引数準備・関数呼び出し全体の一般定理は未証明 |
| E11 識別子引数は既存 Cell を共有 | 未使用引数・強制後の共有を観測 | `lookupEnv` の補題はあるが、引数共有全体は未証明 |
| E12 closure の本体・局所 Scope | 最後の式文、局所再束縛、親 Scope | 呼び出し全体の意味論的正しさは未証明 |
| E13 定義時の生きた Scope | 定義後のグローバル再束縛など | closure の挙動全体は未証明 |
| E14 捕捉時に見えていた束縛の固定 | `b = a + 1; a = 10` で古い参照を使う | **証明あり**: `capture_preserves` / `capture_preserves_under_bind`。保持するのは**アドレス**であり Cell 内容の永久不変性ではない |
| E15 未捕捉名の前方参照 | 作成後の束縛・再束縛 | **証明あり**: `capture_unbound_lookup`、`forward_ref_resolves`、`forward_ref_rebound`。対象 Scope の存在などの条件あり |
| E16 ブラックホール | 自己参照によるエラー・stdout の保存 | **部分的な証明**: `whnf_blackhole`、`whnf_reenter_blackholed`。任意の実行経路での循環検出は未証明 |
| E17 左から右への強制順 | 算術・`print`、左辺エラーなら右辺不実行 | 実行照合のみ。一般的な評価順序定理は未証明 |
| E18 整数算術とゼロ除算 | `n / 0` といくつかの整数演算 | 負数除算などは未対応・未検証。一般定理なし |
| E19 `print` と出力保持 | 全引数の強制後に改行なしで出力 | 出力順・例外時出力保持の一般定理は未証明 |
| E20 `exit` は要求時に終了 | 未評価 `exit` と出力保持 | Bool など一部の値は未対応。一般定理なし |
| E21 エラー位置 | 最も内側の強制点／文頭など | 位置の一般的な正しさは未証明 |
| E22 識別子だけの文 | 強制され、closure なら0引数呼び出し | 組込みの0引数呼び出しは未対応。一般定理なし |

特に **E2 は E1/E11 と独立には観測で区別できず**、E12 の「未評価の戻り値」も現在の9ノードでは独立に区別できない。構文・評価器を増やす前に、このような**観測上の識別可能性**を意識する。

## 3. 証明済みの性質と前提

| 工程・Lean ソース | 主な定理 | どこまで言えるか |
|---|---|---|
| [P2a: Heap](../lean/Les/Proofs/Heap.lean) | `Heap.alloc_cell?_of_valid`、`Heap.setCell_cell?_ne`、`Heap.bind_cell?`、`Heap.bind_lookupLocal_self` | Cell の割当・更新・束縛操作の局所的な性質。更新対象・アドレス有効性などは各定理の前提に従う |
| [P2b: Memo](../lean/Les/Proofs/Memo.lean) | `whnf_done`、`whnf_blackhole`、`whnf_suspended_ok`、`whnf_suspended_ok_cell_valid` | `done` の再強制は無変更、既存 `blackhole` の再強制はエラー。成功した `demand` 後は `done` に変わる |
| [P2c: Capture](../lean/Les/Proofs/Capture.lean) | `capture_preserves`、`forward_ref_resolves`、`forward_ref_rebound` | 捕捉済みのアドレスの固定、未捕捉名の live Scope からの解決。Cell 内容の不変性や Heap 全体の整合性は含まない |
| [P2d-1: WellFormed](../lean/Les/Proofs/WellFormed.lean) | `Heap.initial_structWF`、`Heap.alloc_structWF`、`Heap.setCell_structWF`、`Heap.newScope_structWF`、`Heap.bind_structWF` | `StructWF` は Scope の束縛先・親・親添字の減少の3条件のみ。`bind` には新規アドレスの有効性、`newScope` には親の有効性等が必要 |
| [P2d-2: Monotone](../lean/Les/Proofs/Monotone.lean) | `mono_bind`、`mono_tryCatch`、`mono_validAddr`、`modHeap_not_mono` | Cell 数の**最終状態での非減少性**を合成。任意の `modHeap f` が単調とは主張せず、反例もある |
| [P2d-3: MonotoneEval](../lean/Les/Proofs/MonotoneEval.lean) | `monoAt`、`demand_mono`、`evalE_mono`、`whnf_mono`、`demand_validAddr` | 実際の評価器の相互再帰11関数について fuel の帰納法を使用。正常・例外終了の最終状態まで有効アドレスを保存 |
| [P2d-4: Memo](../lean/Les/Proofs/Memo.lean) | `Machine.blackholed_validAddr`、`demand_blackholed_validAddr`、`whnf_suspended_ok_then_stable_valid` | 初期 `suspended` Cell の存在と `demand` 成功を使い、従来の `hvalid` を外部から仮定せずにメモ化定理へつなぐ |
| [P2d-5: PR #19](https://github.com/gotoken/les-spec/pull/19) | [`whnf_suspended_ok_memo`](https://github.com/gotoken/les-spec/blob/6a7dbc2f651bbc4deaa4be661c86852989f5e6de/lean/Les/Proofs/Memo.lean) | **main 反映済み**。`hrun` / `hvalid` の外部仮定なしで初回強制の成功・`done` への書込・任意の正の fuel による再強制の安定性を統合 |

### P2d-5 の統合定理：正確な条件

定理 `whnf_suspended_ok_memo` が必要とする前提は次の2つ。

1. `m.heap.cell? a = some (.suspended e env)`（開始時に対象 Cell が未評価）
2. `((demand n e env).run).run (m.blackholed a e) = (Except.ok v, m₂)`（ブラックホール状態からの demand が正常終了）

`m₃ := { m₂ with heap := m₂.heap.setCell a (.done v) }` とおくと、結論は以下。

- `whnf (n + 1) a` の実行結果は `(Except.ok v, m₃)`。
- `m₃.heap.cell? a = some (.done v)`。
- すべての `k : Nat` について、`whnf (k + 1) a` を `m₃` から実行すると `(Except.ok v, m₃)`。すなわち値も Machine も変わらない。

**これは demand が必ず成功するという定理ではない。** また、単調性は最終状態の Cell 数についての命題であり、全中間状態の不変性を直接述べるものではない。

### P2d-5 の非空虚性を示す例（PR #20 で追加）

[`lean/Les/Proofs/NonVacuity.lean`](../lean/Les/Proofs/NonVacuity.lean) は、既存の `Heap.initial` に整数リテラル `42` を保持する未評価 Cell を割り当て、同一の具体的な Machine で次を満たすことを示す。

- `memoWitness_suspended`：割り当てたアドレスの Cell は `.suspended e env`。
- `memoWitness_structWF`：この Machine の Heap は既存の `Heap.StructWF`（スコープの構造的整合性）を満たす。
- `memoWitness_demand_ok`：その Cell を `blackhole` に書き換えた状態から `demand 2 e env` が `Except.ok (.int 42)` で終了する。実際の Lean 評価器を `rfl` で計算する。
- `whnf_suspended_ok_memo_nonvacuous`：P2d-5 の**2つの仮定が同時に成立する証人の存在**を、`StructWF` も併せて存在定理として示す。
- `memoWitness_integrated`：既存の `whnf_suspended_ok_memo` を証人へ適用し、初回強制の成功・`done` への書込・任意の正の fuel での再強制の安定性を示す。

**この証人は「条件を満たす例が存在する」ことの確認であり、すべての `demand` が成功するという主張ではない。** また、`StructWF` は Cell 内部の参照までを含む完全な Heap 整合性ではない。

**検証状態:** 新規ファイルは PR #20 に追加済みだが、ここでの `lake build` / `#print axioms` の独立した実行は未確認。マージ前にビルドとアクシオム確認を行う。

## 4. 依存関係

次は意味論上の主要な依存を要約した図であり、Lean の `import` を1対1で写したものではない。

~~~mermaid
flowchart TD
    A["P2a: Heap の局所補題"]
    B["P2b-1/2: whnf の場合分けと done 安定性"]
    C["P2c-1/2: capture / lookupEnv"]
    D["P2d-1: StructWF と基本操作"]
    E["P2d-2: Cell 数単調性と合成"]
    F["P2d-3: 相互再帰11関数・demand_mono"]
    G["P2d-4: demand 後の ValidAddr"]
    H["P2d-5: 成功時メモ化の統合定理（main）"]
    I["PR #20: 非空虚性の具体的な証人"]
    A --> B
    A --> C
    A --> D
    A --> E
    E --> F
    F --> G
    A --> G
    B --> G
    B --> H
    G --> H
    A --> I
    D --> I
    H --> I
~~~

P2c の環境捕捉と P2d のアドレス有効性は、現時点では**別の性質**として証明されている。これらを合わせて言語全体の正しさを保証しているわけではない。

## 5. 今後の検証課題（未達を明示する）

### 最初に行う監査

1. **非空虚性（PR #20 で証人を追加、ビルド要確認）:** P2d-5 の前提 `h` と `hd` を同時に満たす具体的な `Machine` / `Expr` / `Env` / fuel を [`NonVacuity.lean`](../lean/Les/Proofs/NonVacuity.lean) に構成した。マージ前に Lean カーネルによるコンパイルと `#print axioms` を確認する。
2. **対応関係の検査:** 実行器に一時的な意味論の改変を加えた場合、対応する差分テストや定理がどこで検出するかを確認する。証明の前提が自明になっていないかも点検する。
3. **定理の再現性:** PR #19 は main にマージ済み。PR #20 の証人を含め、fresh clone / pinned Lean toolchain で `lake build`、35件比較、41件個別テスト、`#print axioms whnf_suspended_ok_memo_nonvacuous` を実行し、記録する。

### 意味論の次の問い

- `demand` がエラー・`outOfFuel` で終わる場合の Cell/blackhole と stdout の残り方。成功時のメモ化定理をそのまま失敗時に拡張しない。
- `Cell.suspended` の `Env.snap` / `Env.scope`、`Value.closure` の Scope を含むより強い Heap 整合性と、**評価器の各実行経路での保存性**。`StructWF` の保存性だけでは十分でない。
- 構文・実行機能の拡張（`if`、Tuple、Dict、パターンなど）は、観測 → 規則 → Lean モデル → 差分テスト → 必要な証明の順で一機能ずつ進める。
- Go と Lean の一般的な同値性、Go の型推論・型安全性、全機能の正しさは長期的な目標であり、現段階の成果には含めない。

## 6. 計画変更と再現手順への入口

当初の [`PLAN.md`](../PLAN.md) は「P2=機能拡張、P4=定理」を想定していた。実際には、P1 で限定的ながら実行可能なモデルと35件のオラクル比較が揃ったため、**そのモデルを凍結して中核の定理を先に証明する**順序へ変更した。理由と新旧対応は更新後の [PLAN.md](../PLAN.md) を参照。

~~~sh
bash scripts/bootstrap.sh
python3 difftest/run.py
python3 lesdump/test.py
cd lean
lake build
lake exe les-syntax-test ../lesdump/golden 35
lake exe les-eval-test ../lesdump/golden ../difftest/corpus
~~~

コマンドは再現手順であり、**この文書作成 PR 自体で再実行した結果ではない**。個別の実行結果は `tasks/results/` に記録されている。

