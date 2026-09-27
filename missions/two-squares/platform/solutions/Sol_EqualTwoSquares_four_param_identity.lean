-- Public-mission submission for EqualTwoSquares.four_param_identity.

import Mathlib

theorem solution (p q r s : ℤ) :
    (p * r + q * s)^2 + (p * s - q * r)^2 =
      (p * r - q * s)^2 + (p * s + q * r)^2 := by
  ring
