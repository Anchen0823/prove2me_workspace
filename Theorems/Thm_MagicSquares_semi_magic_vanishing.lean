import Mathlib
import Definitions.Def_MagicSquares

set_option autoImplicit false

open MagicSquares

namespace MagicSquares

/-- Local mirror of live Open theorem `2b98befc-35ff-4cd0-be18-2536bf8adae8`.
The placeholder is permitted only to let the root reduction type-check locally. -/
theorem semi_magic_vanishing (n : ℕ) (hn : 1 ≤ n) (p : Polynomial ℚ)
    (hp : ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)) :
    ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) - 1 → p.eval (-(k : ℚ)) = 0 := by
  sorry

end MagicSquares
