import Mathlib

namespace TaoFivePrimes

theorem sieve_log_error_budget (x : ℝ) (hx : 10 ^ 9 ≤ x) :
    2 * Real.sqrt x * Real.log x ≤ x / 150 := by
  have hx0 : 0 ≤ x := by linarith
  have hs := Real.sq_sqrt hx0
  have hs0 := Real.sqrt_nonneg x
  have hslo : 30000 ≤ Real.sqrt x := by nlinarith
  have hl := Real.log_le_sub_one_of_pos
    (show 0 < Real.sqrt x / 10000 by positivity)
  rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt hx0] at hl
  have hlog : Real.log 10000 ≤ 36 := by
    have hten := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
    rw [show (10000 : ℝ) = 10 ^ 4 by norm_num, Real.log_pow]
    norm_num
    linarith
  have hb : Real.log x ≤ Real.sqrt x / 5000 + 70 := by linarith
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * Real.sqrt x by positivity)
  have ht := mul_nonneg hs0 (show 0 ≤ Real.sqrt x - 30000 by linarith)
  nlinarith

end TaoFivePrimes
