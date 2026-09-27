import Mathlib

namespace EqualTwoSquares

/-- Objective 4, parity: after possibly swapping c and d, matching entries have equal parity. -/
theorem parity_alignment {a b c d : ℤ} (h : a^2 + b^2 = c^2 + d^2) :
    (Even (a - c) ∧ Even (b - d)) ∨ (Even (a - d) ∧ Even (b - c)) := by sorry

end EqualTwoSquares
