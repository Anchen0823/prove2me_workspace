import Mathlib

namespace EqualTwoSquares

/-- Brahmagupta–Fibonacci identity, both forms. -/
theorem two_squares_mul {R : Type*} [CommRing R] (p q r s : R) :
    (p^2 + q^2) * (r^2 + s^2) = (p * r + q * s)^2 + (p * s - q * r)^2 ∧
      (p^2 + q^2) * (r^2 + s^2) = (p * r - q * s)^2 + (p * s + q * r)^2 := by sorry

end EqualTwoSquares
