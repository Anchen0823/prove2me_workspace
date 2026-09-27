import Mathlib

namespace EqualTwoSquares

/-- Objective 2, equality part: the explicit one-parameter family, valid for every integer n. -/
theorem explicit_family_identity (n : ℤ) :
    (1 : ℤ)^2 + (n^2 - n + 1)^2 = (2 * n - 1)^2 + (n^2 - n - 1)^2 := by sorry

end EqualTwoSquares
