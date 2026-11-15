/-
P0 の足場 + P1c-1 の構文層。意味論（評価器）はまだ含めない。
固定 upstream: upstream/LES_COMMIT を参照。
-/
import Les.Syntax
import Les.Eval.Eval
import Les.Eval.Observe
import Les.Proofs.Heap
import Les.Proofs.Memo

namespace Les

/-- ビルド確認用の識別子。意味論的な主張は持たない。 -/
def scaffoldVersion : String := "P0"

end Les
