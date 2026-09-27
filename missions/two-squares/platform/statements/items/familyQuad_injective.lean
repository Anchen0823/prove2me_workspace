import Mathlib

namespace EqualTwoSquares

/-- Objective 3: the parametrisation n ↦ (1, n^2-n+1, 2n-1, n^2-n-1) is injective. -/
theorem familyQuad_injective :
    Function.Injective
      (fun n : ℤ => ((1 : ℤ), n^2 - n + 1, 2 * n - 1, n^2 - n - 1)) := by sorry

end EqualTwoSquares
