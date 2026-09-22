import Mathlib
import Definitions.Def_MagicSquares

set_option autoImplicit false

open MagicSquares

namespace MagicSquares

/-- Local mirror of live Open theorem `3dc34529-feed-4b21-bd4f-443097422b63`.
The placeholder is permitted only to let the root reduction type-check locally. -/
theorem semi_magic_polynomial_exists (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : Polynomial ℚ,
      p.natDegree = (n - 1) ^ 2 ∧
        ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ) := by
  sorry

end MagicSquares
