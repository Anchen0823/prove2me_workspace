-- Public-mission submission for EqualTwoSquares.two_squares_mul.
-- Verified locally: see missions/two-squares/platform/statements/ and the combined
-- compile of every solution in missions/two-squares/platform/solutions/check_all.py.

import Mathlib

theorem solution {R : Type*} [CommRing R] (p q r s : R) :
    (p^2 + q^2) * (r^2 + s^2) = (p * r + q * s)^2 + (p * s - q * r)^2 ∧
      (p^2 + q^2) * (r^2 + s^2) = (p * r - q * s)^2 + (p * s + q * r)^2 := by
  constructor <;> ring
