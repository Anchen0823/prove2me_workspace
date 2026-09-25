import Mathlib
import Definitions.Def_MagicSquaresMatchingBoundary
attribute [local instance] Classical.propDecidable
namespace MagicSquares

theorem matching_coefficient_eq_neg_mobius (n : ℕ) (hn : 1 ≤ n)
    (B : Finset (Fin n × Fin n))
    (hB : MagicSquaresBoundary.MatchingCoveredBoard n B) :
    MagicSquaresBoundary.matchingEulerCoefficient n B =
      -IncidenceAlgebra.mu ℚ
        (⟨∅, Or.inl rfl⟩ :
          {C : Finset (Fin n × Fin n) //
            C = ∅ ∨ MagicSquaresBoundary.MatchingCoveredBoard n C})
        ⟨B, Or.inr hB⟩ := by
  sorry

end MagicSquares
