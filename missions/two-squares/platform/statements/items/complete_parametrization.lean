import Mathlib

namespace EqualTwoSquares

/-- Objective 6, the goal: the four-parameter parametrisation is complete. -/
theorem complete_parametrization {a b c d : ℤ} (h : a^2 + b^2 = c^2 + d^2) :
    (∃ p q r s : ℤ,
      a = p * r + q * s ∧ b = p * s - q * r ∧
        c = p * r - q * s ∧ d = p * s + q * r) ∨
      (∃ p q r s : ℤ,
        a = p * r + q * s ∧ b = p * s - q * r ∧
          d = p * r - q * s ∧ c = p * s + q * r) := by sorry

end EqualTwoSquares
