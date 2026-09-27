import Mathlib

namespace EqualTwoSquares

/-- Objective 5: every solution of XY = UV over the integers admits four parameters. -/
theorem four_factor_param (X Y U V : ℤ) (h : X * Y = U * V) :
    ∃ p q r s : ℤ, X = p * r ∧ Y = q * s ∧ U = p * s ∧ V = q * r := by sorry

end EqualTwoSquares
