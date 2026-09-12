import Mathlib

namespace TaoFivePrimes

/-- A rational series bound used for the critical finite endpoint. -/
theorem log_two_upper_certificate : Real.log 2 ≤ 0.693147181 := by
  have h := Real.log_div_le_sum_range_add
    (show (0 : ℝ) ≤ 1 / 3 by norm_num)
    (show (1 / 3 : ℝ) < 1 by norm_num) 10
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- Rounded upward using integer arithmetic, then bounded by the log series. -/
theorem log_critical_mantissa_upper :
    Real.log ((159679 : ℝ) / 125000) ≤ 0.24485182 := by
  have h := Real.log_div_le_sum_range_add
    (show (0 : ℝ) ≤ 34679 / 284679 by norm_num)
    (show (34679 / 284679 : ℝ) < 1 by norm_num) 5
  norm_num [Finset.sum_range_succ] at h
  linarith

set_option maxRecDepth 4096 in
/-- Exact arithmetic identifies the least common multiple at the tight endpoint. -/
theorem lcm_upto_113_certificate :
    Nat.lcmUpto 113 = 955888052326228459513511038256280353796626534577600 := by
  decide

/-- The numerically tight endpoint is checked without floating point assumptions. -/
theorem rosser_at_113 : Chebyshev.psi (113 : ℝ) < 1.03883 * 113 := by
  rw [show (113 : ℝ) = (113 : ℕ) by norm_num,
    Chebyshev.psi_eq_log_lcmUpto, lcm_upto_113_certificate]
  have hround : (955888052326228459513511038256280353796626534577600 : ℝ) ≤
      2 ^ 169 * (159679 / 125000) := by norm_num
  have hlog := Real.log_le_log
    (by norm_num : (0 : ℝ) < 955888052326228459513511038256280353796626534577600) hround
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog
  have htwo := log_two_upper_certificate
  have hm := log_critical_mantissa_upper
  norm_num at hlog ⊢
  linarith

end TaoFivePrimes
