import Definitions.Def_eulerMascheroni_sondow
open EulerMascheroni.Sondow
theorem EulerMascheroni.Sondow.scaled_integral_bounds (n : ℕ) (hn : 0 < n) :
    0 < (d (2*n) : ℝ) * I n ∧ (d (2*n) : ℝ) * I n < (1/2 : ℝ)^n := by sorry
