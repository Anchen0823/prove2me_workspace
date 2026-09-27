import Mathlib

namespace EqualTwoSquares

/-- Objective 2, inequality part: the four entries form a strict chain for every n at least 4. -/
theorem explicit_family_chain {n : ℤ} (hn : 4 ≤ n) :
    (1 : ℤ) < 2 * n - 1 ∧
      2 * n - 1 < n^2 - n - 1 ∧
        n^2 - n - 1 < n^2 - n + 1 := by sorry

end EqualTwoSquares
