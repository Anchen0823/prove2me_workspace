import Definitions.Def_eulerMascheroni_sondow
open EulerMascheroni.Sondow
theorem EulerMascheroni.Sondow.fractional_lower_bound_conjecture :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 0 < n ∧
      (1/2 : ℝ)^n ≤ Int.fract ((d (2*n) : ℝ) * L n) := by sorry
