import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace TaoFivePrimes

/-- The coarse integer Hilbert bound still fits the required 2q budget. -/
theorem unit_kernel_constant (q h : ℝ) (hq : 40 ≤ q)
    (hh : (q - 1) / q ^ 2 ≤ h) :
    1 + (7 / 2 : ℝ) / (Real.pi * h) + q / 2 ≤ 2 * q := by
  have hq0 : 0 < q := by linarith
  have hδ : 0 < (q - 1) / q ^ 2 := div_pos (by linarith) (sq_pos_of_pos hq0)
  have hh0 : 0 < h := hδ.trans_le hh
  have hp : 0 < Real.pi * h := mul_pos Real.pi_pos hh0
  have hh' : q - 1 ≤ h * q ^ 2 := (div_le_iff₀ (sq_pos_of_pos hq0)).mp hh
  have hc : 0 ≤ 3 * q / 2 - 1 := by linarith
  have hmain : (7 / 2 : ℝ) ≤ (3 * q / 2 - 1) * (Real.pi * h) := by
    have ha := mul_le_mul_of_nonneg_left hh' (show 0 ≤ 3 * (3 * q / 2 - 1) by positivity)
    have hb := mul_le_mul_of_nonneg_right Real.pi_gt_three.le
      (mul_nonneg hc hh0.le)
    have hpoly := mul_nonneg hq0.le (show 0 ≤ q - 8 by linarith)
    have ht : (7 / 2 : ℝ) * q ^ 2 ≤ ((3 * q / 2 - 1) * (3 * h)) * q ^ 2 := by
      nlinarith
    have ht' : (7 / 2 : ℝ) ≤ (3 * q / 2 - 1) * (3 * h) :=
      (mul_le_mul_iff_left₀ (sq_pos_of_pos hq0)).mp (by nlinarith [ht])
    nlinarith
  have hf := (div_le_iff₀ hp).mpr hmain
  linarith

/-- A half-modulus block lies inside the interval where the cosecant error
is at most one. -/
theorem unit_kernel_angle (q h t : ℝ) (hq : 100 ≤ q) (hh0 : 0 ≤ h)
    (hh : h ≤ (q + 1) / q ^ 2) (ht : |t| ≤ q / 2) :
    |(Real.pi * h) * t| ≤ 8 / 5 := by
  have hq0 : 0 < q := by linarith
  have h1 : h * q ≤ (q + 1) / q := by
    have hb := (le_div_iff₀ (sq_pos_of_pos hq0)).mp hh
    apply (le_div_iff₀ hq0).mpr
    nlinarith [hb]
  have h2 : h * q ≤ (101 / 100 : ℝ) := by
    have hb : (q + 1) / q ≤ (101 / 100 : ℝ) := by
      apply (div_le_iff₀ hq0).mpr
      linarith
    exact h1.trans hb
  rw [abs_mul, abs_of_nonneg (mul_nonneg Real.pi_pos.le hh0)]
  have ha := mul_le_mul_of_nonneg_left ht (mul_nonneg Real.pi_pos.le hh0)
  have hb := mul_le_mul_of_nonneg_left h2 Real.pi_pos.le
  have hc := Real.pi_lt_d2
  nlinarith

end TaoFivePrimes
