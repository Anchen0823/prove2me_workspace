import Mathlib

namespace TaoFivePrimes

set_option exponentiation.threshold 2048

theorem log_two_upper_for_lcm : Real.log 2 ≤ 0.693147181 := by
  have h := Real.log_div_le_sum_range_add
    (show (0 : ℝ) ≤ 1 / 3 by norm_num)
    (show (1 / 3 : ℝ) < 1 by norm_num) 10
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- Integer upper bounds on the LCM give certified bounds for psi. -/
theorem psi_le_of_lcm_le_power (n k : ℕ)
    (h : Nat.lcmUpto n ≤ 2 ^ k) :
    Chebyshev.psi (n : ℝ) ≤ (k : ℝ) * 0.693147181 := by
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hp : (0 : ℝ) < Nat.lcmUpto n := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.lcmUpto_ne_zero n)
  have hr : (Nat.lcmUpto n : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast h
  have hl := Real.log_le_log hp hr
  rw [Real.log_pow] at hl
  exact hl.trans (mul_le_mul_of_nonneg_left log_two_upper_for_lcm (Nat.cast_nonneg k))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
theorem lcm_1000_upper : Nat.lcmUpto 1000 ≤ 2 ^ 1438 := by decide

theorem rosser_at_1000 : Chebyshev.psi (1000 : ℝ) < 1.03883 * 1000 := by
  have h := psi_le_of_lcm_le_power 1000 1438 lcm_1000_upper
  norm_num at h ⊢
  linarith

/-- A power certificate can retain extra fractional bits at tight endpoints. -/
theorem psi_mul_le_of_lcm_power (n d k : ℕ)
    (h : Nat.lcmUpto n ^ d ≤ 2 ^ k) :
    (d : ℝ) * Chebyshev.psi (n : ℝ) ≤ (k : ℝ) * 0.693147181 := by
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hp : (0 : ℝ) < (Nat.lcmUpto n : ℝ) ^ d := by
    exact pow_pos (by exact_mod_cast Nat.lcmUpto_pos n) d
  have hr : (Nat.lcmUpto n : ℝ) ^ d ≤ (2 : ℝ) ^ k := by exact_mod_cast h
  have hl := Real.log_le_log hp hr
  rw [Real.log_pow, Real.log_pow] at hl
  exact hl.trans (mul_le_mul_of_nonneg_left log_two_upper_for_lcm (Nat.cast_nonneg k))

theorem rosser_interval_of_power (a b k : ℕ)
    (h : Nat.lcmUpto b ≤ 2 ^ k)
    (hc : (k : ℝ) * 0.693147181 < 1.03883 * (a : ℝ))
    (y : ℝ) (ha : (a : ℝ) ≤ y) (hb : y ≤ (b : ℝ)) :
    Chebyshev.psi y < 1.03883 * y := by
  have hp := (Chebyshev.psi_mono hb).trans (psi_le_of_lcm_le_power b k h)
  have hm : 1.03883 * (a : ℝ) ≤ 1.03883 * y := by gcongr
  exact lt_of_le_of_lt hp (lt_of_lt_of_le hc hm)

end TaoFivePrimes
