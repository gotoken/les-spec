# Lean 評価器の設計メモ（P1c-2）

状態: **設計のみ**。実装コード・証明・対応構文の追加は含まない。固定 upstream は `upstream/LES_COMMIT`（`aa78fdcf…`）。
ここでの「確認済み（CLI）」は固定コミットの Go CLI を実際に実行した観測、「確認済み（ソース）」は `.work/upstream-les/pkg/eval/` を局所的に読んだ結果、「未確定」はどちらでも確かめていないことを指す。

## 1. 位置づけと信頼境界

- 入力は `Les.Syntax.CheckedProgram`（`lean/Les/Syntax/AST.lean`）。`analysis.status = ok` の証明つきで、型エラーのプログラムは型の上で渡せない。
- **`CheckedProgram` は「Go の型検査が通った」という結果を信頼する境界であり、Lean による型安全性の証明ではない。** Lean 側は型を再検査せず、型注釈（文字列）も読まない。したがって評価器は「型の合わない演算」に当たった場合でも停止する（`Halt.error`）よう全域に作る。Go の型検査が保証する前提（引数の型など）に評価結果が依存する箇所は、その前提を明記して扱う。
- 評価器は fuel によって必ず停止する純関数 `run : Nat → CheckedProgram → Outcome` とする。I/O は実行せず、標準出力を文字列として蓄積する。
- 対象は現在の `lesdump` の 9 ノード（`Ident` / `Int` / `String` / `Binary` / `Force` / `Call` / `ExprStmt` / `VarDecl` / `FuncDef`）のみ。組込みは `print` と `exit` だけ。

## 2. Go 実装で確認できた規則

用語: Go の `Thunk`（`pkg/eval/value.go`）は `{Evaluated, Value, Expr, Env, Evaluating}`。`Force` は未評価 Thunk を一度だけ評価して結果を保存し、評価中に再度要求されると `blackhole` で panic する。

### 2.1 確認済みの規則

最小再現は ⏎ を改行とした 1 行表記。CLI 欄の `/` の位置は列番号を示す。

| ID | 規則 | 最小再現（観測） | 根拠 |
|---|---|---|---|
| E1 | 変数束縛は右辺が **リテラルでも Force でもなければ**未評価 Thunk を作る。評価されなければエラーも出ない | `x = 1 / 0`⏎`print "ok"` → `ok`、exit 0 | CLI（`lazy-unused-binding`）、ソース: `evalStmt` の `VarDecl` |
| E2 | 要求時評価: 変数の**参照そのもの**は評価しない（Thunk のまま返す）。`print` / 算術 / `exit` などが値を要求した時だけ評価する | `v = id(1 / 0)`⏎`print "after;"`⏎`print v`（`id(a) = a`）→ stdout `after;`、`print v` で division by zero | CLI、ソース: `evalExpr` の `Identifier`（`env.Get` の結果をそのまま返す） |
| E3 | **再束縛**（同じスコープに既にある名前への `x = ...`）は右辺を**その場で強制評価**し、評価済みの値で置き換える。遅延させない | `x = 1`⏎`x = 1 / 0`⏎`print "ok"` → エラー（`:2: division by zero at col 7`）、exit 1、stdout 空。対照: 初回束縛 `x = 1 / 0` はエラーにならない | CLI、ソース: `VarDecl` の `if _, ok := env.store[s.Name]` 分岐（コメント: 循環参照を避けるため） |
| E4 | 再束縛の右辺は**古い束縛**を参照できる | `x = 1`⏎`x = x + 1`⏎`print x` → `2`。`x = 5`⏎`x = x + 1`⏎`x = x * 2` → `12` | CLI |
| E5 | 再束縛されなかった古い Thunk は評価されない | `x = 1 / 0`⏎`x = 2`⏎`print x` → `2`、exit 0 | CLI |
| E6 | **明示的 force**（prefix `force e` / postfix `e!` は同じ `Force` ノード）は、それが現れた式の評価時に**その場で** `e` を強制評価する。束縛の右辺なら束縛の時点、引数なら呼び出し時点（使われない引数でも） | `x = (1 / 0)!`⏎`print "ok"` → エラー、exit 1（`force-postfix-unused-binding`）。`pick(42, force (1 / 0))`（`pick(a, b) = a`）→ エラー（`force-prefix-unused-arg`）。対照: `pick(42, 1 / 0)` → `42` | CLI（corpus）、ソース: `isForceDemand` / `CallExpr` の引数処理 |
| E7 | prefix `force` は直後の項だけを強制する | `c = force 50 + 60` は `(force 50) + 60` で `110` | CLI（`force-basic`）、`lesdump`（AST-001） |
| E8 | 通常の遅延束縛と明示 force の違いは「いつ評価されるか」だけ。結果の値は同じ | `a = (10 + 20)!` と `b = (10 + 20)` はどちらも `30` | CLI（`force-basic`） |
| E9 | **Thunk は共有・メモ化される**: 同じ Thunk を何度要求しても副作用は 1 回 | `def g(): Int: print "side;"; 1` に対し `x = g()`⏎`print "before;"`⏎`print x`⏎`print x` → `before;side;11` | CLI（Thunk が評価結果を保存する `Force` のソースとも一致） |
| E10 | 引数は未評価 Thunk（by need）で渡り、仮引数と呼び出し側で**共有**される。引数の副作用は 1 回 | `twice(a) = a + a` に `twice(g())` → `side;2` | CLI |
| E11 | 引数がリテラルなら評価済みの値、識別子なら**既存の束縛そのもの**（新しい Thunk を作らない）、force なら強制評価結果、それ以外は未評価 Thunk | `n = 1 / 0`⏎`f(n)`（本体 `1`）→ `1`、エラーなし | CLI（`t31`）、ソース: `CallExpr` / `newCapturedThunk` |
| E12 | 呼び出し（`def`）の評価: 呼び出し元に関係なく、**定義時のスコープ（生きたもの）**の子スコープを作り、仮引数を束縛して本体を実行する。本体の値は**最後の式文の値**（文が無い・束縛だけなら空タプル）で、**未評価の Thunk のまま**返りうる | `v = id(1 / 0)` は呼び出しではエラーにならない（E2 の再現と同じ）。`y = 3`⏎`f()`（本体 `y`）→ `3`、`y = 4` の後は `4` | CLI、ソース: `invokeClosure` / `evalBlock` |
| E13 | 関数本体のスコープは定義時のグローバルスコープを**参照し続ける**。後からの再束縛は見える | 上の `f()` が `3` → `4` | CLI（`t19`） |
| E14 | Thunk は**作った時点で見えていた束縛をスナップショット**する（参照する名前だけをコピー。値は不変なので参照のコピーで足りる）。作った後の再束縛は、その Thunk からは見えない | `a = 1`⏎`b = a + 1`⏎`a = 10`⏎`print b` → `2` | CLI、ソース: `capture.go` の `captureEnv` |
| E15 | スナップショットに**含まれなかった名前**（作った時点で未束縛）は、**評価時**にスコープから引かれる。前方参照が効き、評価時点の最新の束縛が見える | `b = a + 1`⏎`a = 5`⏎`print b` → `6`。`b = a + 1`⏎`a = 5`⏎`a = 7`⏎`print b` → `8` | CLI（`t6`, `t18`）、ソース: `captureEnv` の「未束縛の名前は親に任せる」 |
| E16 | 評価中の Thunk を再び要求すると**ブラックホール**: 実行時エラー `blackhole: circular reference detected in lazy thunk`（位置情報なし）、exit 1。それまでの出力は残る | `x = x + 1`⏎`print "ok"`⏎`print x` → stdout `ok`、stderr `Runtime Error: blackhole: …` | CLI（`t5`）、ソース: `Force` |
| E17 | 算術 `+ - * /`（Int）は**両オペランドを左から右へ強制**してから計算する。Int は任意精度（Go は `big.Int`） | `print 1, g()` は `g;11`（`g` の副作用が `print` の出力より先） | CLI、ソース: `evalExpr` の `BinaryExpr` |
| E18 | `n / 0` は `division by zero`。`7 / 2 = 3` | `print 7 / 2` → `3` | CLI |
| E19 | `print` は**全引数を左から右へ強制**し、連結して**末尾改行なし**で書き出し、即座にフラッシュする。値は空タプル | `print "a"`⏎`print 1 / 0` → stdout `a` が**残り**、exit 1 | CLI、ソース: `registerBuiltins` の `print`（`Flush` を呼ぶ） |
| E20 | `exit(n)` は引数を強制して終了コードにする（`Int` / `Bool`）。**要求された時点で**終了する（束縛だけでは終了しない）。それまでの出力は残る | `x = exit(7)`⏎`print "a"`⏎`print x` → stdout `a`、exit 7 | CLI、ソース: `ExitError` |
| E21 | **エラー位置**: 実行時エラーのメッセージは `<file>:<行>: <メッセージ> at col <列>`。位置は、エラーが起きた時に**強制中だった最も内側の Thunk（`Force` する式）の位置**、そのような式が無ければ**囲む文の先頭位置**。二項式の位置は演算子の位置 | `print 5 + (1 / 0)` → col 14（`/`）。裸の文 `1 / 0` → col 1（文頭）。関数本体の裸の `1 / 0` → `:2:` col 5（文頭） | CLI（`t27`〜`t30`、corpus の 4 件）、ソース: `FormatRuntimeError` と `Force` |

### 2.2 未確定（今回の設計では扱わない／仮置き）

- **ExprStmt が識別子 1 つだけで、それが関数の場合は 0 引数で自動呼び出しされる**（`evalStmt` の `isCallableTarget`）。コーパスの範囲（`first` のような Int 引数）では起きないので、最初は未実装として明示的に `Halt.error` にする。
- Int の `/` の負数の丸め、オーバーフロー以外の例外、`+` の String への適用などの型依存の演算: 未観測。実装時は Int×Int のみ対応し、他は `Halt.error "unsupported"`。
- `referencedNames`（スナップショットに入れる名前）は Go では**過大近似**（入れ子のラムダの束縛名なども含む）。観測可能な違いが出る例は見つかっていない。Lean では自由変数の過大近似なら何でもよいとし、細部は一致させない。
- 型情報（`InferredType`）が評価結果に影響する箇所（`print` の `Show` チェックなど）は、型検査済みなら起きないという前提。9 ノード・golden の範囲では結果に影響しないが、一般には**未検証**。
- スタック深さ（Go の再帰の上限）、並行処理、`Producer` Thunk（I/O）、他のノード全般は対象外。

## 3. データ型（Lean のスケッチ）

`lean/` に実装はまだ置かない。以下の型は一時ファイルで Lean 4.25.0 によりコンパイルできること（型定義の整合）だけ確認した。`opaque` の署名は省略している。

```lean
namespace Les.Eval
abbrev Addr := Nat          -- Cell の番号
abbrev ScopeId := Nat       -- Scope の番号

inductive Builtin where | print | exit

inductive Value where
  | int (i : Int)
  | str (s : String)
  | unit                                   -- 空タプル（print の値、束縛だけの本体の値）
  | builtin (b : Builtin)
  | closure (params : List Param) (body : List Stmt) (scope : ScopeId)  -- def。scope は定義時の「生きた」スコープ

/-- Thunk の環境。snap が先に引かれ、無ければ scope の「現在の」中身を引く（E14, E15）。 -/
structure Env where
  snap : List (String × Addr)
  scope : ScopeId

inductive Cell where
  | done (v : Value)                       -- 評価済み（リテラル、強制済みの Thunk、組込み、closure）
  | suspended (e : Expr) (env : Env)       -- 未評価 Thunk
  | blackhole (e : Expr)                   -- 評価中（再要求でエラー: E16）

structure Scope where
  vars : List (String × Addr)              -- 「現在の」束縛。再束縛で置き換わる（E3）
  parent : Option ScopeId                  -- ルートは組込み（print, exit）を持つ

structure Heap where
  cells : Array Cell
  scopes : Array Scope

/-- エラーの位置の状態。「位置待ち」と「意図的に位置なし」を区別する（E16, E21）。 -/
inductive ErrPos where
  | pending                                -- まだ位置が無い。最も内側の demand / whnf / exec が一度だけ付ける
  | absent                                 -- 意図的に位置を持たない（ブラックホール）。何も付けない
  | at (p : Pos)                           -- 付与済み。上書きしない

inductive Halt where
  | exit (code : Int)                      -- E20
  | error (msg : String) (pos : ErrPos)
  | outOfFuel                              -- Go に対応物は無い。差分テストでは「結論なし」

structure Machine where
  heap : Heap
  stdout : String                          -- 出力はここに溜める。`Halt` でも残る（E19, E20）

/-- **ExceptT が外側、状態が内側**。`Halt` を投げても `Machine`（stdout と Heap）は失われず、
    実行結果は `(Except Halt α, Machine)` として成功・失敗どちらでも最終状態を返す。
    逆順の `StateT Machine (Except Halt)` だと投げた時点で状態が捨てられ、E19・E20 が出せない。 -/
abbrev EvalM := ExceptT Halt (StateM Machine)

structure Outcome where
  stdout : String
  halt : Option Halt                       -- none = 正常終了
end Les.Eval
```

署名（実装時に書く。ここでは名前と型だけ）:

```lean
-- evalE   : Nat → Expr → Env → EvalM Addr          式を評価して Cell を返す（Thunk のままでもよい: E2）
-- whnf    : Nat → Addr → EvalM Value                Cell を強制して値にする（Go の Force: 共有・メモ化・blackhole）
-- demand  : Nat → Expr → Env → EvalM Value          = evalE して whnf（Go の Force(NewThunk(e, env)))
-- exec    : Nat → Stmt → ScopeId → EvalM (Option Addr)   文を実行。値を返すのは ExprStmt だけ（E12）
-- run     : Nat → CheckedProgram → Outcome
```

設計の要点:

- **名前は常に Cell を指す**。`Value` を直接持たず、評価済みかどうかは `Cell` が持つ。同じ `Addr` を共有すれば共有・メモ化が成り立つ（E9, E10）。
- **スコープを Heap に置く**。Go の `Environment.store` は可変で、再束縛は同じ `store` を書き換える。これを `Scope.vars` の更新として表す。Thunk の `Env` は `snap`（作成時点の束縛のコピー）と `scope`（生きたスコープ）の 2 層にして、E14（作成後の再束縛は見えない）と E15（未束縛だった名前は評価時の最新を見る）を同時に満たす。純粋な永続的環境だけではこの 2 つを同時に出せない（E15 の `a = 7` の例で 6 ではなく 8 になる）。
- `Value.closure.scope` も `ScopeId`（生きたスコープ）にして E13 を満たす。

## 4. 評価手順

停止性は **fuel を構造再帰の引数にする**ことで確保する（Lean の関数を `partial` にしない）。`evalE` / `whnf` / `exec` は fuel が 0 なら `throw Halt.outOfFuel`、そうでなければ `n+1` として、再帰呼び出しには `n` を渡す。

- fuel は**呼び出しの入れ子の深さ**の上限であり、総ステップ数の上限ではない。非停止は再帰（`def` の自己呼び出し）か循環参照でしか起きず、どちらも深さを増やす。循環参照は E16 のブラックホールで検出するので fuel は使わない。
- 総ステップ数が指数的に増える病的なプログラムは fuel だけでは抑えられない。最初の実装では golden の小さなプログラムしか扱わないので許容し、問題になったら状態にステップ数の予算を足す。
- `outOfFuel` は Go との比較では「結論なし」とし、PASS にも FAIL にもしない。

### 4.1 式

| ノード | 手順 |
|---|---|
| `Int` / `String` | 評価済み Cell（`done`）を新規確保（E11） |
| `Ident n` | `snap`、なければ `scope` の現在の束縛を引く。**強制しない**。見つからなければ `Halt.error "undefined identifier: n"`（型検査済みなら到達しない） |
| `Binary op l r`（`+ - * /`） | `demand l`、次に `demand r`（E17）。両方 `Int` なら計算して `done` Cell。`/` で右が 0 なら `division by zero`。それ以外の型は `unsupported`（2.2） |
| `Force e` | `demand e env` を**今**行い、結果を `done` Cell で返す（E6） |
| `Call f args` | `demand f` で呼び先の値を得る。次に引数を**左から**準備する: `Int`/`String` リテラル → `done`、`Ident` → 既存の Cell（E11）、`Force` → `demand` した値の `done`、それ以外 → `suspended a (capture a scope)`（E10, E11） |
| 呼び先が `builtin print` | 全引数を左から `whnf`（E19）し、`Int` と `String` を連結して `stdout` に足す。戻り値は `unit`。他の型は `unsupported` |
| 呼び先が `builtin exit` | 0 引数なら 0、1 引数なら `whnf` して `Int`（または Bool）を終了コードにし `Halt.exit`（E20） |
| 呼び先が `closure` | 子スコープを `closure.scope` の下に作り、仮引数名を引数の Cell に束縛（引数が足りなければ `unit`）して本体を `execBlock`（E12） |

`capture e scope`: `e` の自由変数名（過大近似でよい: 2.2）のうち、**今 `scope` の連鎖で見つかるもの**だけを `snap` に入れる。見つからない名前は入れない（E15）。ただし `e` が `Ident n` で `n` が束縛済みなら、新しい Cell を作らず既存の Cell をそのまま使う（E11）。

### 4.2 強制 `whnf`

`whnf a` は Cell で場合分けする。

- `done v` → `v`。
- `suspended e env` → Cell を `blackhole e` に書き換え、`demand e env` を行い（結果が別の Cell なら `whnf` で辿る）、得た値で Cell を `done v` に書き換える（**メモ化**: E9。Go では `Thunk.Env` も解放する）。
- `blackhole _` → `Halt.error "blackhole: circular reference detected in lazy thunk" ErrPos.absent`（E16。**意図的に位置を持たない**ので、以降どの層も位置を付けない）。

エラー位置（E21）: 算術のエラー（`division by zero`）や `unsupported` などの原始的なエラーは `ErrPos.pending` で投げる。`whnf` / `demand` は、`pending` のエラーを受け取った時に**その式の位置を付けて `at` にする**。`exec` は、文まで `pending` のまま上がってきたエラーに**その文の位置を付ける**。**`at` と `absent` は変えない**（Go の `FormatRuntimeError` が、すでに整形済みのメッセージを再整形しないのに対応する）。`Binary` の位置は `lesdump` の `pos`（演算子の位置）をそのまま使う。不変条件: `run` が返す時点で `pending` のエラーは残らない（最外の `exec` が必ず付けるため）。ブラックホールは `absent` で投げるので、位置は付かない。

### 4.3 文

- `VarDecl n _ rhs`（`scope` で）:
  1. **`n` が `scope` の現在の束縛に既にある（再束縛）**: `demand rhs`（スナップショットなし。評価は今行うので不要）→ `done v` を `n` に束縛し直す（E3, E4）。
  2. そうでなく `rhs` が `Int`/`String` リテラル: `done` を束縛（Go と同様。観測上は区別できない）。
  3. そうでなく `rhs` が `Force _`: `demand` して `done` を束縛（E6）。
  4. それ以外: `suspended rhs (capture rhs scope)` を束縛（E1）。
  再束縛の判定は**そのスコープだけ**（親スコープは見ない。Go の `env.store`）。親にしか無い名前への `x = ...` は新しい局所束縛を作り、親は変わらない（確認済み（CLI）: `x = 1`⏎`def f(): Int: x = 2; x`⏎`print f(), ";", x` → `2;1`）。
- `FuncDef n params ret body`: `done (closure params body scope)` を束縛。型注釈は無視（1 節）。
- `ExprStmt e`: `evalE e`。値（Cell のまま）を文の値とする。識別子だけの文が関数のときの自動呼び出しは**未対応**（2.2）。

ブロックの値は、値を返した最後の `ExprStmt` の Cell。1 つも無ければ `unit`（E12）。トップレベルは全文を実行し、`Halt` が出たら止める。

### 4.4 修正後の設計での期待結果（3 ケース）

状態は `ExceptT Halt (StateM Machine)` なので、どのケースでも `Halt` が出た時点の `Machine.stdout` が `Outcome.stdout` になる。

以下の 3 ケースの結果は、`ErrPos`・`Halt`・`EvalM` と「`pending` だけに位置を付ける」層を最小限に写した玩具モデル（評価器ではない、リポジトリには置かない）を Lean 4.25.0 で実行し、下に書いた比較形式の出力になることを確認した。

**(1) `exit-status`**（`print "ok"`⏎`exit(7)`）
1. 1 文目: `print` が `"ok"` を `Machine.stdout` に足す（`stdout = "ok"`）。
2. 2 文目: `exit` を呼び先に評価し、引数 `7` を強制して `Halt.exit 7` を投げる。状態は外側の `StateM` に残る。
3. `Outcome = { stdout := "ok", halt := some (.exit 7) }` → 比較形式 `{"stdout":"ok","stderr":"","exit_code":7}`。`exit-status.expect.json` と一致する（修正前の積み順だと `stdout` が空になり一致しない）。

**(2) 出力後の実行時エラー**（`print "a"`⏎`print 1 / 0`。CLI 観測は E19）
1. 1 文目: `stdout = "a"`。
2. 2 文目: `print` が引数の Thunk（`1 / 0`、位置は `/` の 2 行 9 列）を `whnf` する。`demand` が `1` と `0` を強制し、`/` が `Halt.error "division by zero" .pending` を投げる。
3. その Thunk の `whnf` / `demand` が `pending` を受け取り、式の位置を付けて `.at (2, 9)` にする。上の層（`exec`）は `at` なので変えない。
4. `Outcome = { stdout := "a", halt := some (.error "division by zero" (.at ⟨2, 9⟩)) }` → `{"stdout":"a","stderr":"Runtime Error: <CASE>:2: division by zero at col 9\n","exit_code":1}`。Go の観測（stdout `a`、`:2: division by zero at col 9`、exit 1）と一致する。

**(3) ブラックホール**（`x = x + 1`⏎`print "ok"`⏎`print x`。CLI 観測は E16）
1. 1 文目: `x` は `scope` に未束縛なので `snap` に入らず、`suspended (x + 1)` の Cell `c` を `x` に束縛する（E1, E15）。
2. 2 文目: `stdout = "ok"`。
3. 3 文目: `print` が `c` を `whnf` する。`c` を `blackhole` にして `x + 1` を `demand` する。左の `x` を引くと `scope` の現在の束縛 `c` が見つかり、`whnf c` は `blackhole` に当たって `Halt.error "blackhole: circular reference detected in lazy thunk" .absent` を投げる。
4. 上の層（`whnf` / `demand` / `exec`）は `absent` なので**位置を付けない**。
5. `Outcome = { stdout := "ok", halt := some (.error "blackhole: …" .absent) }` → `{"stdout":"ok","stderr":"Runtime Error: blackhole: circular reference detected in lazy thunk\n","exit_code":1}`。Go の観測（stdout `ok`、位置なし、exit 1）と一致する。
- 注: この例は変数に型注釈が無く Go が `Type Warning` を stderr に出す（`t5` で観測）。コーパスに追加する時は警告の出ない書き方を探す必要がある（未確認）。

## 5. Go CLI と Lean の比較形式

`difftest/corpus/*.expect.json` と同じ形に揃える。**1 つの共通の正規化済み形**を Go 側（`run.py` の観測）と Lean 側（`run` の結果）の両方が出し、`stdout` / `exit_code` / `stderr` を厳密に比較する。

```json
{ "stdout": "30 70 110", "stderr": "", "exit_code": 0 }
```

- `Halt.exit c` → `exit_code = c`、`stderr = ""`。`halt = none` → `exit_code = 0`。
- `Halt.error msg (.at pos)` → `exit_code = 1`、`stderr = "Runtime Error: <CASE>:<line>: <msg> at col <col>\n"`（`<CASE>` は `run.py` がケースのパスを置換する記号と同じ）。`Halt.error msg .absent`（ブラックホール）→ `stderr = "Runtime Error: <msg>\n"`。`.pending` は `run` から出てこない（4.2 節の不変条件）。`stdout` は `Machine.stdout` で、`Halt` の種類によらず常に出す。
- Go の `Type Warning` は stderr に出るので、golden の期待値は**型注釈付き**（警告なし）に限る（P0 の方針と同じ）。
- `outOfFuel` は比較対象外（「結論なし」として別集計）。
- Lean 側の実行ファイルは `lesdump` の JSON を読み、上の JSON を標準出力に出す。比較は既存の `difftest/run.py` に「Lean の出力と Go の観測を突き合わせるモード」を足して行う想定（実装は次タスク）。

## 6. golden 10 件の実装順

10 件はすべて 9 ノードの範囲内で、型注釈付き（警告なし）。ただし必要な機構が違うので 2 段階に分ける。

**段階 A（最初の実装対象。クロージャなし、7 件）**: スコープは 1 つ（グローバル）、`Cell` / `whnf` / `capture` / `print` / `exit` だけで足りる。

| ケース | 使う規則 |
|---|---|
| `basic-print` | E1, E17, E19 |
| `print-no-newline` | E19 |
| `exit-status` | E19, E20 |
| `div-zero-control` | E18, E21 |
| `lazy-unused-binding` | E1 |
| `force-postfix-unused-binding` | E6, E21 |
| `force-basic` | E6, E7, E8 |

**段階 B（次の対象。`def` と呼び出し、3 件）**: `Value.closure`、引数の Cell 共有（E10, E11）、子スコープ（E12）が要る。

| ケース | 使う規則 |
|---|---|
| `lazy-unused` | E10, E12 |
| `force-postfix-unused-arg` | E6, E10, E21 |
| `force-prefix-unused-arg` | E6, E10, E21 |

**golden に無い規則（段階 C）**: 再束縛（E3〜E5）、スナップショットと前方参照（E14, E15）、メモ化と共有（E9, E10）、ブラックホール（E16）、関数本体からのグローバル参照（E13）、`exit` の遅延（E20）、エラー位置の一般則（E21）は、現在の golden では**ほとんど検証されない**。2.1 の最小再現を `difftest/corpus/` に型注釈付きで足す（`lesdump` の 9 ノードに収まる）。**E3〜E5, E9, E10, E14〜E16, E19〜E21 は P1c-3 で 12 件を追加済み**（対応表は `difftest/corpus/README.md`）。E11〜E13, E17, E18 はまだコーパスに無い。これを足さないと、この設計の中核（Heap・スコープ・snap）が正しいかどうかを Go との比較で確かめられない。

## 7. 設計判断とその根拠

| 判断 | 採用 | 理由・却下した案 |
|---|---|---|
| 環境の表現 | Thunk の `Env` を `snap` + 生きた `scope` の 2 層にする | Go の `captureEnv` と同じ観測（E14, E15）が必要。永続的な環境だけでは E15 の「評価時の最新の束縛」を出せず、可変なスコープだけでは E14 を出せない |
| 名前の指すもの | 常に `Addr`（Cell） | 共有・メモ化（E9, E10）を `Addr` の同一性で表せる。`Value` を直接持つ案は共有を表せない |
| 再束縛 | 右辺を即時評価し `done` で置き換え | Go の挙動（E3）。遅延にすると循環参照になる（コメントの理由と一致） |
| 停止性 | fuel を構造再帰の引数にする。`partial` にしない | 後の証明（停止性、遅延の健全性）を妨げない。代償は総ステップ数を抑えられないこと（4 節） |
| 出力 | `Machine.stdout` に溜め、エラー・終了でも残す | E19, E20。比較形式（5 節）の `stdout` にそのまま出る |
| エラー位置 | `ErrPos` の 3 状態（`pending` / `absent` / `at`）。`pending` だけを `whnf` / `demand` / `exec` が一度だけ `at` にする | Go の `FormatRuntimeError`（メッセージに ` at col ` が含まれていれば何もしない）と同じ冪等性に加え、ブラックホールのように**意図的に位置が無い**エラー（Go では整形されない panic）を区別するため。`Option Pos` だと「位置待ち」と「位置なし」が区別できない（Codex レビュー指摘） |
| モナドの積み順 | `ExceptT Halt (StateM Machine)` | `Halt` を投げても `Machine`（stdout）を残すため。`StateT Machine (Except Halt)` だと状態が捨てられ、`exit` やエラーの前の出力が出せない（Codex レビュー指摘。Lean で `exit` 相当を投げて確認済み） |
| 型 | 評価器は読まない | 1 節。Go の型検査結果を信頼する境界に留め、Lean 側で型安全性を主張しない |

`semantics-opus` には問い合わせなかった。複数の合理的な候補が割れる論点（環境の表現）は、Go の観測（E14, E15）で一意に決まったため。

## 8. 次のタスク候補

1. 2.1 の最小再現のうち E3〜E5, E9〜E10, E14〜E16, E20, E21 を型注釈付きのコーパスとして追加し、`lesdump` の golden を作る（9 ノードの範囲内。Go の観測だけで、Lean の実装はまだ要らない）。
2. その後に段階 A の評価器を実装する。
