/-
P0/P1c から発展した Les のライブラリ入口。
構文層、実行可能な評価器、P2a〜P2d-5 の証明と非空虚性の証人を import する。
固定 upstream: upstream/LES_COMMIT を参照。
-/
import Les.Syntax
import Les.Eval.Eval
import Les.Eval.Observe
import Les.Proofs.Heap
import Les.Proofs.Memo
import Les.Proofs.Capture
import Les.Proofs.WellFormed
import Les.Proofs.Monotone
import Les.Proofs.MonotoneEval
import Les.Proofs.NonVacuity

namespace Les

/-- P0 で作ったビルド確認用の識別子。値 "P0" は歴史的な名前で、
    現在の実装段階を示すバージョン番号ではない。意味論的な主張は持たない。 -/
def scaffoldVersion : String := "P0"

end Les
