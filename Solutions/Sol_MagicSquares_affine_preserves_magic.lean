import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresTransforms

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

/-- Every line has `n` entries, so its sum becomes `a * s + n • b`. -/
theorem solution {n : ℕ} {α : Type*} [Semiring α]
    (M : Square n α) (s a b : α) (hM : IsMagic M s) :
    IsMagic (affine a b M) (a * s + n • b) := by
  constructor
  · constructor
    · intro i
      simpa [rowSum_affine, hM.1.1 i]
    · intro j
      simpa [colSum_affine, hM.1.2 j]
  · constructor
    · simpa [diagSum_affine, hM.2.1]
    · simpa [antiDiagSum_affine, hM.2.2]
