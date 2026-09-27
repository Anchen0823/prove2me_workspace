import Mathlib

namespace EqualTwoSquares

/-- Objective 3: the family produces infinitely many distinct quadruples. -/
theorem family_patterns_infinite :
    (Set.range (fun n : ℤ => ((1 : ℤ), n^2 - n + 1, 2 * n - 1, n^2 - n - 1))).Infinite := by sorry

end EqualTwoSquares
