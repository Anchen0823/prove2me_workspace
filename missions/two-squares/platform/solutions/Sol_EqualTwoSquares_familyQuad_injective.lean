-- Public-mission submission for EqualTwoSquares.familyQuad_injective.

import Mathlib

theorem solution :
    Function.Injective
      (fun n : ℤ => ((1 : ℤ), n^2 - n + 1, 2 * n - 1, n^2 - n - 1)) := by
  intro m n h
  have hlin : 2 * m - 1 = 2 * n - 1 := by
    simpa using congrArg (fun t : ℤ × ℤ × ℤ × ℤ => t.2.2.1) h
  omega
