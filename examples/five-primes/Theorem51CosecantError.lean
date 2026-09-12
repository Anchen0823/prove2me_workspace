import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

namespace TaoFivePrimes

/-- A coarse but sufficient Hilbert-kernel approximation on a half-circle. -/
lemma cosecant_sub_inv_le_one (t : ℝ) (ht : 0 < t) (hmax : t ≤ 8 / 5) :
    |1 / Real.sin t - 1 / t| ≤ 1 := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_gt_three])
  have hsle : Real.sin t ≤ t := Real.sin_le ht.le
  have hnonneg : 0 ≤ 1 / Real.sin t - 1 / t := by
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le hs hsle
  rw [abs_of_nonneg hnonneg]
  have hsq : t ^ 2 ≤ (8 / 5 : ℝ) ^ 2 := (sq_le_sq₀ ht.le (by norm_num)).mpr hmax
  have hpoly : 0 ≤ 6 - t - t ^ 2 := by nlinarith
  have hmul : 0 ≤ t ^ 2 * (6 - t - t ^ 2) := mul_nonneg (sq_nonneg _) hpoly
  have hsin := Real.sin_ge_sub_cube ht.le
  have hprod := mul_le_mul_of_nonneg_right hsin (show 0 ≤ 1 + t by linarith)
  have hmain : t ≤ (1 + t) * Real.sin t := by nlinarith
  apply (sub_le_iff_le_add).mpr
  apply (div_le_iff₀ hs).mpr
  rw [show (1 + 1 / t) * Real.sin t = ((1 + t) * Real.sin t) / t by field_simp; ring]
  exact (le_div_iff₀ ht).mpr (by simpa using hmain)

lemma abs_cosecant_sub_inv_le_one (t : ℝ) (ht : t ≠ 0) (hmax : |t| ≤ 8 / 5) :
    |1 / Real.sin t - 1 / t| ≤ 1 := by
  rcases lt_or_gt_of_ne ht with ht | ht
  · have h := cosecant_sub_inv_le_one (-t) (by linarith) (by simpa [abs_of_neg ht] using hmax)
    simpa only [Real.sin_neg, div_neg, neg_sub_neg, abs_sub_comm] using h
  · exact cosecant_sub_inv_le_one t ht (by simpa [abs_of_pos ht] using hmax)

end TaoFivePrimes
