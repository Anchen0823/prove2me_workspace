import Definitions.Def_eulerMascheroni_sondow
open EulerMascheroni.Sondow
theorem EulerMascheroni.Sondow.integral_identity (n : ℕ) (hn : 0 < n) :
    I n = ((2*n).choose n : ℝ) * Real.eulerMascheroniConstant + L n - (A n : ℝ) := by sorry
