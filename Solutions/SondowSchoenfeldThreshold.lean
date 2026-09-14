import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! Endpoint conversion for the first row of the Rosser--Schoenfeld (1975)
error table. This proves only the logarithmic threshold, not a prime estimate. -/

namespace EulerMascheroni.Sondow

theorem log_ge_table_start (y : ℝ) (hy : (10 : ℝ) ^ 8 ≤ y) :
    (18.42 : ℝ) ≤ Real.log y := by
  have hlog : (18.42 : ℝ) ≤ Real.log ((10 : ℝ) ^ 8) := by
    rw [Real.log_pow, Real.log_ten_eq]
    have h2 := Real.log_two_gt_d9
    have h5 := Real.log_five_gt_d9
    norm_num only [Nat.cast_ofNat]
    linarith
  exact hlog.trans (Real.log_le_log (by norm_num) hy)

end EulerMascheroni.Sondow

#print axioms EulerMascheroni.Sondow.log_ge_table_start
