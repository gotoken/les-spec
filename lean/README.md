# Lean の実装・証明構成（P2d-5 時点）

このディレクトリには、[`unak/les`](https://github.com/unak/les) の固定コミットを対象にした
**限定的な実行可能評価器**と、その評価器の定義に対する Lean の証明がある。
P0 当時の「足場のみ」「評価器・定理は後で実装」という記述は現在には当てはまらない。

成果の適用範囲、証明済み／未証明の区別、E1〜E22 の対応表は
[`docs/proof-coverage.md`](../docs/proof-coverage.md) を参照。

## 現在のファイル構成

~~~text
lean/
├── lean-toolchain            # Lean 4.25.0
├── lakefile.toml             # Les ライブラリと2種類のテスト実行ファイル
├── Les.lean                  # 構文・評価器・証明のライブラリ入口
├── Les/
│   ├── Syntax.lean
│   ├── Syntax/
│   │   ├── AST.lean          # 式6種・文3種、型解析結果、CheckedProgram
│   │   ├── Decode.lean       # lesdump JSON → Lean AST
│   │   └── Encode.lean       # AST → JSON（往復テスト用）
│   ├── Eval/
│   │   ├── Types.lean        # Value, Cell, Env, Scope, Heap, Machine, Halt
│   │   ├── Heap.lean         # 割当、参照、再束縛、親スコープ探索
│   │   ├── Eval.lean         # fuel 付き評価器、Thunk/closure、組込み
│   │   └── Observe.lean      # stdout/stderr/exit_code の正規化
│   └── Proofs/
│       ├── Heap.lean         # P2a: Heap の基本操作
│       ├── Memo.lean         # P2b, P2d-4/5: 初回強制、メモ化、再強制
│       ├── Capture.lean      # P2c: 捕捉済み／未捕捉名の参照
│       ├── WellFormed.lean   # P2d-1: 構造的な Heap 整合性
│       ├── Monotone.lean     # P2d-2: Cell 数単調性の合成補題
│       ├── MonotoneEval.lean # P2d-3: 評価器11関数の単調性
│       └── NonVacuity.lean  # P2d-5: 統合定理の2前提を満たす実例
└── Tests/
    ├── Main.lean             # JSON AST のデコード・再エンコード等
    └── Eval.lean             # Go CLI のコーパス35件との比較・個別テスト
~~~

P0 当初に想定していた `Core/`、`Thm/`、`IO.lean`、`Main.lean` は実際の配置ではない。
現在の名前は上記の `Syntax/`、`Eval/`、`Proofs/`、`Tests/` を使用する。

## 評価器とその境界

- Go 側のパーサー・型解析が出力した `lesdump` JSON を読み込み、`CheckedProgram` を評価する。Lean が Go の型推論を証明したわけではない。
- 対応する構文は現在のコーパスに必要な**式6種類・文3種類**。Les の全機能は扱わない。
- `Env.snap` には作成時に捕捉した名前→Cell アドレスを置き、捕捉されなかった名前は生きた Scope から解決する。
- Cell は `suspended`／`blackhole`／`done` を持ち、`whnf` は要求時に強制し成功結果を共有・メモ化する。
- 評価器の再帰は fuel により停止させる。fuel は実行ステップの総数ではない。
- `EvalM = ExceptT Halt (StateM Machine)` なので、例外になっても以前の Heap や stdout の変更は残る。
- **評価器の `evalE`・`whnf`・`demand` と関連する相互再帰関数は全域定義**で、`partial` を使わない。一方、**JSON の再帰デコーダーやエンコーダーには `partial def` がある**。この二者を混同しない。

## 検証

Lean 4.25.0 と Lake を利用できる環境で、リポジトリのルートから次を実行する。

~~~sh
bash scripts/bootstrap.sh
python3 difftest/run.py
python3 lesdump/test.py
cd lean
lake build
lake exe les-syntax-test ../lesdump/golden 35
lake exe les-eval-test ../lesdump/golden ../difftest/corpus
~~~

- `difftest/run.py` は固定 Go CLI のオラクル期待値を照合する。
- `les-eval-test` は AST JSON をデコードして Lean 評価器を実行し、35件すべての観測結果（stdout、stderr、exit_code）を期待値と照合する。`stageA` の19件は履歴表示上の区分であり、段階Bを含めて35件すべて PASS が必要。
- Lean 個別テスト41件、構文・デコードテストの結果は工程ごとの `tasks/results/` を参照。ここにあるコマンドは**再現手順**であって、README の更新時に再実行した証拠ではない。
- `NonVacuity.lean` では P2d-5 の `whnf_suspended_ok_memo` の前提を満たす具体的な整合的 Heap と、統合定理の適用を示す。`#print axioms` による検査行も同ファイルにある。

## 証明が保証すること、保証しないこと

Heap の基本操作、捕捉済みアドレスの保存・未捕捉名の前方参照、Cell 数の単調性、**成功した**初回強制のメモ化と再強制の安定性などは**この Lean 評価器の定義について**証明した。

ただし、以下は保証しない。

- Go 実装とのすべての入力での意味論的同値性（35件の差分テストは有限の観測）。
- すべての `demand` が成功すること、失敗後のメモ化。
- Cell 内部の参照を含む完全な Heap 整合性。`StructWF` はスコープの構造だけを扱う。
- 元の Les 全体の型安全性・終了性。

P0 でのセットアップや Lean toolchain 取得時の回避策は [`tasks/results/P0.md`](../tasks/results/P0.md) を参照。

