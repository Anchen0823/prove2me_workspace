import Mathlib
import Definitions.Def_MagicSquaresRealCone
import Definitions.Def_MagicSquaresMatchingBoundary
namespace MagicSquares

theorem real_cone_face_support_order_iso (n : ℕ) (hn : 1 ≤ n) :
    ∃ e :
      {F : PointedCone ℝ ((Fin n × Fin n) → ℝ) //
        F.IsFaceOf (MagicSquaresRealCone.cone n)} ≃o
      {B : Finset (Fin n × Fin n) //
        B = ∅ ∨ MagicSquaresBoundary.MatchingCoveredBoard n B},
      ∀ F i, i ∈ (e F).val ↔ ∃ x ∈ F.val, x i ≠ 0 := by
  sorry

end MagicSquares
