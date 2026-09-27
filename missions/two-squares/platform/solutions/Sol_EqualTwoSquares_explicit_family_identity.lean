-- Public-mission submission for EqualTwoSquares.explicit_family_identity.

import Mathlib

theorem solution (n : ℤ) :
    (1 : ℤ)^2 + (n^2 - n + 1)^2 = (2 * n - 1)^2 + (n^2 - n - 1)^2 := by
  ring
