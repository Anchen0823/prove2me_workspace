import examples.«five-primes».Theorem51CutoffAmplitude
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

namespace TaoFivePrimes

/-- The logarithmic coefficient never exceeds log x on the cutoff support. -/
lemma typeI_log_coefficient_bound (x d y : ℝ) (c : ℂ)
    (hd : 1 ≤ d) (hy : 1 ≤ y) (hxy : d * y ≤ x) (hc : ‖c‖ ≤ 1) :
    ‖(Real.log y : ℂ) + c * (Real.log d : ℂ)‖ ≤ Real.log x := by
  have hd0 : 0 < d := by linarith
  have hy0 : 0 < y := by linarith
  have hld : 0 ≤ Real.log d := Real.log_nonneg hd
  have hly : 0 ≤ Real.log y := Real.log_nonneg hy
  calc
    _ ≤ ‖(Real.log y : ℂ)‖ + ‖c * (Real.log d : ℂ)‖ := norm_add_le _ _
    _ = Real.log y + ‖c‖ * Real.log d := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg hly, abs_of_nonneg hld]
    _ ≤ Real.log y + Real.log d := by nlinarith
    _ = Real.log (d * y) := by rw [Real.log_mul hd0.ne' hy0.ne']; ring
    _ ≤ Real.log x := Real.log_le_log (mul_pos hd0 hy0) hxy

/-- Each smooth piece of the logarithmic amplitude has this universal form. -/
lemma log_product_hasDerivAt (y : ℝ) (hy : y ≠ 0) (b k : ℂ) :
    HasDerivAt (fun t : ℝ => 4 * ((Real.log t : ℂ) + k) * ((Real.log t : ℂ) + b))
      (4 / (y : ℂ) * (2 * (Real.log y : ℂ) + b + k)) y := by
  have h := (((Real.hasDerivAt_log hy).ofReal_comp.add_const k).const_mul 4).mul
    ((Real.hasDerivAt_log hy).ofReal_comp.add_const b)
  convert h using 1 <;> first | rfl | (simp only [Complex.ofReal_inv, div_eq_mul_inv]; ring)

lemma log_product_derivative_hasDerivAt (y : ℝ) (hy : y ≠ 0) (b k : ℂ) :
    HasDerivAt (fun t : ℝ => 4 / (t : ℂ) * (2 * (Real.log t : ℂ) + b + k))
      (4 / (y : ℂ) ^ 2 * (2 - 2 * (Real.log y : ℂ) - b - k)) y := by
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  have h := ((hasDerivAt_const y (4 : ℂ)).div
    (hasDerivAt_id y).ofReal_comp hyC).mul
      ((((Real.hasDerivAt_log hy).ofReal_comp.const_mul 2).add_const b).add_const k)
  convert h using 1 <;> first | rfl | (simp only [Pi.div_apply, id_eq,
    Complex.ofReal_one, Complex.ofReal_inv]; field_simp; ring)

/-- A uniform majorant for the curvature of either logarithmic piece.
Here L is the logarithm in the cutoff and g is the logarithmic coefficient. -/
lemma typeI_curvature_majorant (y X L : ℝ) (g : ℂ) (hy : 0 < y)
    (hg : ‖g‖ ≤ X) (hL : |L| ≤ 3 / 4) :
    ‖(4 / (y : ℂ) ^ 2) * (2 - g - (L : ℂ))‖ ≤ (4 * X + 11) / y ^ 2 := by
  have hb : ‖(2 : ℂ) - g - (L : ℂ)‖ ≤ 2 + X + 3 / 4 := by
    calc
      _ ≤ ‖(2 : ℂ) - g‖ + ‖(L : ℂ)‖ := norm_sub_le _ _
      _ ≤ (‖(2 : ℂ)‖ + ‖g‖) + ‖(L : ℂ)‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ 2 + X + 3 / 4 := by
        norm_num [Complex.norm_real, Real.norm_eq_abs]
        linarith
  have he : ‖(4 : ℂ) / (y : ℂ) ^ 2‖ = 4 / y ^ 2 := by
    simp [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  rw [norm_mul, he]
  calc
    _ ≤ (4 / y ^ 2) * (2 + X + 3 / 4) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- Exact integral of the regular-curvature majorant over the cutoff support. -/
lemma typeI_curvature_majorant_integral (r X : ℝ) (hr : 0 < r) :
    (∫ y in r / 4..r, (4 * X + 11) / y ^ 2) = (12 * X + 33) / r := by
  have hz : (0 : ℝ) ∉ Set.uIcc (r / 4) r := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  have hi := integral_zpow (a := r / 4) (b := r) (n := (-2 : ℤ))
    (Or.inr ⟨by norm_num, hz⟩)
  norm_num at hi
  have he (y : ℝ) : (4 * X + 11) / y ^ 2 = (4 * X + 11) * y ^ (-2 : ℤ) := by
    simp [zpow_neg, div_eq_mul_inv]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  simp only [zpow_neg, zpow_ofNat]
  rw [hi]
  field_simp
  ring

/-- The three slope jumps contribute at most 36 log(x)/r.
Together with the regular-curvature integral there is room in 48 log(4x)/r.
The passage from this budget to discrete variation is a separate obligation. -/
lemma typeI_curvature_and_jump_budget (x r : ℝ) (hx : 0 < x) (hr : 0 < r) :
    (12 * Real.log x + 33) / r + 36 * Real.log x / r ≤
      48 * Real.log (4 * x) / r := by
  have hl4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hx.ne', hl4]
  apply (le_div_iff₀ hr).2
  field_simp
  nlinarith [Real.log_two_gt_d9]

lemma typeI_amplitude_lower_formula (r d y : ℝ) (c : ℂ)
    (hr : 0 < r) (hy : 0 < y) (hlo : 1 / 4 ≤ y / r) (hhi : y / r ≤ 1 / 2) :
    ((Real.log y : ℂ) + c * (Real.log d : ℂ)) * (eta0 (y / r) : ℂ) =
      4 * ((Real.log y : ℂ) + (Real.log (4 / r) : ℂ)) *
        ((Real.log y : ℂ) + c * (Real.log d : ℂ)) := by
  rw [eta0_lower_piece hlo hhi,
    show 4 * (y / r) = y * (4 / r) by ring,
    Real.log_mul hy.ne' (by positivity : (4 : ℝ) / r ≠ 0)]
  push_cast
  ring

lemma typeI_amplitude_upper_formula (r d y : ℝ) (c : ℂ)
    (hr : 0 < r) (hy : 0 < y) (hlo : 1 / 2 ≤ y / r) (hhi : y / r ≤ 1) :
    ((Real.log y : ℂ) + c * (Real.log d : ℂ)) * (eta0 (y / r) : ℂ) =
      -4 * ((Real.log y : ℂ) - (Real.log r : ℂ)) *
        ((Real.log y : ℂ) + c * (Real.log d : ℂ)) := by
  rw [eta0_upper_piece hlo hhi, Real.log_div hy.ne' hr.ne']
  push_cast
  ring

/-- The slope jumps at r/4, r/2, and r have weights 16, 16, and 4. -/
lemma typeI_jump_norm_budget (r X : ℝ) (A B C : ℂ) (hr : 0 < r)
    (hA : ‖A‖ ≤ X) (hB : ‖B‖ ≤ X) (hC : ‖C‖ ≤ X) :
    ‖(16 / (r : ℂ)) * A‖ + ‖(16 / (r : ℂ)) * B‖ + ‖(4 / (r : ℂ)) * C‖ ≤
      36 * X / r := by
  have h16 : ‖(16 : ℂ) / (r : ℂ)‖ = 16 / r := by
    simp [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have h4 : ‖(4 : ℂ) / (r : ℂ)‖ = 4 / r := by
    simp [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  simp only [norm_mul, h16, h4]
  calc
    _ ≤ (16 / r) * X + (16 / r) * X + (4 / r) * X := by gcongr
    _ = _ := by ring

/-- The exact one-sided slope at the left endpoint. -/
lemma typeI_left_endpoint_slope (r : ℝ) (hr : 0 < r) (b : ℂ) :
    4 / ((r / 4 : ℝ) : ℂ) *
      (2 * (Real.log (r / 4) : ℂ) + b + (Real.log (4 / r) : ℂ)) =
      (16 / (r : ℂ)) * ((Real.log (r / 4) : ℂ) + b) := by
  rw [Real.log_div hr.ne' (by norm_num), Real.log_div (by norm_num) hr.ne']
  push_cast
  field_simp
  ring

/-- The exact slope jump at the interior corner. -/
lemma typeI_middle_slope_jump (r : ℝ) (hr : 0 < r) (b : ℂ) :
    (-4 / ((r / 2 : ℝ) : ℂ) * (2 * (Real.log (r / 2) : ℂ) + b - (Real.log r : ℂ))) -
      (4 / ((r / 2 : ℝ) : ℂ) *
        (2 * (Real.log (r / 2) : ℂ) + b + (Real.log (4 / r) : ℂ))) =
      (-16 / (r : ℂ)) * ((Real.log (r / 2) : ℂ) + b) := by
  have hl4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [Real.log_div hr.ne' (by norm_num), Real.log_div (by norm_num) hr.ne', hl4]
  push_cast
  field_simp
  ring

lemma typeI_right_endpoint_slope (r : ℝ) (b : ℂ) :
    -4 / (r : ℂ) * (2 * (Real.log r : ℂ) + b - (Real.log r : ℂ)) =
      (-4 / (r : ℂ)) * ((Real.log r : ℂ) + b) := by ring

end TaoFivePrimes
