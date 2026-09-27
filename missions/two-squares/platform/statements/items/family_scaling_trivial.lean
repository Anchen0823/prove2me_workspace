import Mathlib

namespace EqualTwoSquares

/-- Objective 3: no member of the family is a nontrivial integer multiple of another. -/
theorem family_scaling_trivial {m n k : ℤ}
    (h : ((1 : ℤ), n^2 - n + 1, 2 * n - 1, n^2 - n - 1) =
      k • ((1 : ℤ), m^2 - m + 1, 2 * m - 1, m^2 - m - 1)) :
    n = m := by sorry

end EqualTwoSquares
