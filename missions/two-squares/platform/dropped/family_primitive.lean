import Mathlib

namespace EqualTwoSquares

/-- Every member of the family is primitive: the four entries have gcd one. -/
theorem family_primitive (n : ℤ) :
    Int.gcd (Int.gcd (1 : ℤ) (n^2 - n + 1)) (Int.gcd (2 * n - 1) (n^2 - n - 1)) = 1 := by sorry

end EqualTwoSquares
