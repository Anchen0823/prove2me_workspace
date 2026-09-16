import Mathlib

namespace TaoFivePrimes

lemma log_four_le_two_transfer : Real.log 4 ≤ 2 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have he : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  linarith

lemma psi_le_six_transfer (z : ℝ) (hz : 0 ≤ z) : Chebyshev.psi z ≤ 6 * z := by
  have h := Chebyshev.psi_le_const_mul_self hz
  have hc : (Real.log 4 + 4) * z ≤ 6 * z := by
    gcongr
    linarith [log_four_le_two_transfer]
  exact h.trans hc

lemma psi_le_three_large_transfer (z : ℝ) (hz : 4096 ≤ z) :
    Chebyshev.psi z ≤ 3 * z := by
  have hz0 : 0 < z := by linarith
  have hroot : (8 : ℝ) ≤ z ^ (1 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (8 : ℝ) ^ (4 : ℕ))
      (show (8 : ℝ) ^ (4 : ℕ) ≤ z by norm_num; linarith) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h
    norm_num at h
    exact h
  have hlog : Real.log z ≤ 4 * z ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_rpow_div hz0.le (by norm_num : (0 : ℝ) < 1 / 4)
    convert h using 1 <;> ring
  have hmain : Real.log 4 * z ≤ 2 * z :=
    mul_le_mul_of_nonneg_right log_four_le_two_transfer hz0.le
  have herr : 2 * Real.sqrt z * Real.log z ≤ z := by
    calc
      _ ≤ 2 * Real.sqrt z * (4 * z ^ (1 / 4 : ℝ)) := by gcongr
      _ = 8 * z ^ (3 / 4 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        rw [show (3 / 4 : ℝ) = 1 / 2 + 1 / 4 by norm_num, Real.rpow_add hz0]
        ring
      _ ≤ z ^ (1 / 4 : ℝ) * z ^ (3 / 4 : ℝ) := by gcongr
      _ = z := by rw [← Real.rpow_add hz0]; norm_num
  have h := Chebyshev.psi_le (show 1 ≤ z by linarith)
  linarith

lemma psi_sub_theta_le_four_sqrt_transfer (x : ℝ) (hx : 10 ^ 20 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 4 * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hs : (4096 : ℝ) ≤ Real.sqrt x := by
    apply (Real.le_sqrt (by norm_num) hx0.le).2
    norm_num
    linarith
  have hroot : (12 : ℝ) ≤ x ^ (1 / 6 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (12 : ℝ) ^ (6 : ℕ))
      (show (12 : ℝ) ^ (6 : ℕ) ≤ x by norm_num; linarith) (by norm_num : (0 : ℝ) ≤ 1 / 6)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h
    norm_num at h
    exact h
  have hsmall : 12 * x ^ (1 / 3 : ℝ) ≤ Real.sqrt x := by
    calc
      _ ≤ x ^ (1 / 6 : ℝ) * x ^ (1 / 3 : ℝ) := by gcongr
      _ = Real.sqrt x := by rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow]; norm_num
  have horder : x ^ (1 / 5 : ℝ) ≤ x ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have h := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have h2 := psi_le_three_large_transfer (Real.sqrt x) hs
  have h3 := psi_le_six_transfer (x ^ (1 / 3 : ℝ)) (by positivity)
  have h5 := psi_le_six_transfer (x ^ (1 / 5 : ℝ)) (by positivity)
  rw [Real.sqrt_eq_rpow] at h2
  simp only [one_div] at h2 h3 h5 hsmall horder
  rw [Real.sqrt_eq_rpow] at hsmall ⊢
  norm_num at h h2 h3 h5 hsmall horder ⊢
  linarith

end TaoFivePrimes
