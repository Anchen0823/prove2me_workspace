import examples.«five-primes».Theorem51VariationControl
import examples.«five-primes».Theorem51AmplitudeCalculus

namespace TaoFivePrimes

/-- Variation of one logarithmic slope piece, with its inverse-square
curvature integrated exactly rather than replaced by a uniform bound. -/
theorem log_slope_variation_bound (a b X k : ℝ) (c : ℂ)
    (ha : 0 < a) (hX : 0 ≤ X)
    (hcoef : ∀ y ∈ Set.Icc a b, ‖(Real.log y : ℂ) + c‖ ≤ X)
    (hcut : ∀ y ∈ Set.Icc a b, |Real.log y + k| ≤ 3 / 4) :
    eVariationOn (fun y : ℝ => 4 / (y : ℂ) * (2 * (Real.log y : ℂ) + c + (k : ℂ)))
      (Set.Icc a b) ≤ ENNReal.ofReal ((4 * X + 11) * (a⁻¹ - b⁻¹)) := by
  let C : ℝ := 4 * X + 11
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hB (y : ℝ) (hy : y ≠ 0) :
      HasDerivAt (fun t : ℝ => -C / t) (C / y ^ 2) y := by
    have h := (hasDerivAt_const y (-C)).div (hasDerivAt_id y) hy
    convert h using 1 <;> first | rfl | simp
  have h := variation_interval_of_derivative_control
    (fun y : ℝ => 4 / (y : ℂ) * (2 * (Real.log y : ℂ) + c + (k : ℂ)))
    (fun y : ℝ => 4 / (y : ℂ) ^ 2 * (2 - 2 * (Real.log y : ℂ) - c - (k : ℂ)))
    (fun y : ℝ => -C / y) (fun y : ℝ => C / y ^ 2) a b
    (fun y hy => log_product_derivative_hasDerivAt y (ne_of_gt (ha.trans_le hy.1)) c k)
    (fun y hy => hB y (ne_of_gt (ha.trans_le hy.1)))
    (by
      intro y hy
      have hh := typeI_curvature_majorant y X (Real.log y + k) ((Real.log y : ℂ) + c)
        (ha.trans_le hy.1) (hcoef y hy) (hcut y hy)
      convert hh using 1 <;> first | rfl | (push_cast; congr 1; ring))
    (by
      intro u hu v hv huv
      dsimp
      rw [neg_div, neg_div]
      exact neg_le_neg (div_le_div_of_nonneg_left hC (ha.trans_le hu.1) huv))
  convert h using 1
  congr 1
  dsimp [C]
  ring

lemma abs_log_ratio_short (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hba : b ≤ 2 * a) :
    |Real.log b - Real.log a| ≤ 3 / 4 := by
  have hb : 0 < b := ha.trans_le hab
  have hlog0 : 0 ≤ Real.log b - Real.log a := sub_nonneg.mpr (Real.log_le_log ha hab)
  rw [abs_of_nonneg hlog0, ← Real.log_div hb.ne' ha.ne']
  have hlog2 := Real.log_le_log (div_pos hb ha) ((div_le_iff₀ ha).mpr (by linarith : b ≤ 2 * a))
  linarith [Real.log_two_lt_d9]

lemma lower_cutoff_log_bound (r y : ℝ) (hr : 0 < r) (hy : y ∈ Set.Icc (r / 4) (r / 2)) :
    |Real.log y + Real.log (4 / r)| ≤ 3 / 4 := by
  have h := abs_log_ratio_short (r / 4) y (by positivity) hy.1 (by linarith [hy.2])
  have he : Real.log (4 / r) = -Real.log (r / 4) := by
    rw [Real.log_div (by norm_num) hr.ne', Real.log_div hr.ne' (by norm_num)]
    ring
  simpa only [he, sub_eq_add_neg] using h

lemma upper_cutoff_log_bound (r y : ℝ) (hr : 0 < r) (hy : y ∈ Set.Icc (r / 2) r) :
    |Real.log y + -Real.log r| ≤ 3 / 4 := by
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity : 0 < r / 2) hy.1
  have h := abs_log_ratio_short y r hy0 hy.2 (by linarith [hy.1])
  simpa only [← sub_eq_add_neg, abs_sub_comm] using h

lemma variation_neg (f : ℝ → ℂ) (s : Set ℝ) :
    eVariationOn (fun y => -f y) s = eVariationOn f s := by
  simp only [eVariationOn, edist_dist, dist_eq_norm, neg_sub_neg, norm_sub_rev]

noncomputable def typeIPiecewiseSlope (r d : ℝ) (c : ℂ) : ℝ → ℂ :=
  joinedSlope
    (fun y => 4 / (y : ℂ) * (2 * (Real.log y : ℂ) + c * (Real.log d : ℂ) + (Real.log (4 / r) : ℂ)))
    (fun y => -4 / (y : ℂ) * (2 * (Real.log y : ℂ) + c * (Real.log d : ℂ) - (Real.log r : ℂ)))
    (r / 4) (r / 2) r

/-- The actual zero-extended piecewise slope has the required variation budget. -/
theorem typeI_piecewise_slope_variation (r d : ℝ) (c : ℂ)
    (hr : 4 ≤ r) (hd : 1 ≤ d) (hc : ‖c‖ ≤ 1) :
    eVariationOn (typeIPiecewiseSlope r d c) Set.univ ≤
      ENNReal.ofReal (48 * Real.log (4 * (d * r)) / r) := by
  have hr0 : 0 < r := by linarith
  have hd0 : 0 < d := by linarith
  let X := Real.log (d * r)
  let C := 4 * X + 11
  let b0 : ℂ := c * (Real.log d : ℂ)
  let L (y : ℝ) := 4 / (y : ℂ) * (2 * (Real.log y : ℂ) + b0 + (Real.log (4 / r) : ℂ))
  let R (y : ℝ) := -4 / (y : ℂ) * (2 * (Real.log y : ℂ) + b0 - (Real.log r : ℂ))
  have hX : 0 ≤ X := Real.log_nonneg (by nlinarith)
  have hC : 0 ≤ C := by dsimp [C]; linarith
  have hcoef (y : ℝ) (hy : y ∈ Set.Icc (r / 4) r) : ‖(Real.log y : ℂ) + b0‖ ≤ X := by
    apply typeI_log_coefficient_bound (d * r) d y c hd (by linarith [hy.1]) _ hc
    exact mul_le_mul_of_nonneg_left hy.2 hd0.le
  have hL : eVariationOn L (Set.Icc (r / 4) (r / 2)) ≤ ENNReal.ofReal (2 * C / r) := by
    have h := log_slope_variation_bound (r / 4) (r / 2) X (Real.log (4 / r)) b0
      (by positivity) hX (fun y hy => hcoef y ⟨hy.1, by linarith [hy.2]⟩)
      (fun y hy => lower_cutoff_log_bound r y hr0 hy)
    convert h using 1
    congr 1
    dsimp [C]
    field_simp
    ring
  have hR : eVariationOn R (Set.Icc (r / 2) r) ≤ ENNReal.ofReal (C / r) := by
    let P (y : ℝ) := 4 / (y : ℂ) * (2 * (Real.log y : ℂ) + b0 + ((-Real.log r : ℝ) : ℂ))
    have he : R = fun y => -P y := by
      funext y
      dsimp [R, P]
      push_cast
      ring
    rw [he, variation_neg]
    have h := log_slope_variation_bound (r / 2) r X (-Real.log r) b0
      (by positivity) hX (fun y hy => hcoef y ⟨by linarith [hy.1], hy.2⟩)
      (fun y hy => upper_cutoff_log_bound r y hr0 hy)
    convert h using 1
    congr 1
    dsimp [C]
    field_simp
    ring
  have hj : ‖L (r / 4)‖ + ‖R (r / 2) - L (r / 2)‖ + ‖R r‖ ≤ 36 * X / r := by
    have h := typeI_jump_norm_budget r X
      ((Real.log (r / 4) : ℂ) + b0) ((Real.log (r / 2) : ℂ) + b0)
      ((Real.log r : ℂ) + b0) hr0
      (hcoef _ ⟨le_rfl, by linarith⟩) (hcoef _ ⟨by linarith, by linarith⟩)
      (hcoef _ ⟨by linarith, le_rfl⟩)
    dsimp [L, R]
    rw [typeI_left_endpoint_slope r hr0 b0, typeI_middle_slope_jump r hr0 b0,
      typeI_right_endpoint_slope r b0]
    simpa only [neg_div, neg_mul, norm_neg] using h
  have h := joinedSlope_variation_budget L R (r / 4) (r / 2) r (2 * C / r) (C / r)
    (by linarith) (by linarith) (by positivity) (by positivity) hL hR
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  have hb := typeI_curvature_and_jump_budget (d * r) r (mul_pos hd0 hr0) hr0
  have he : 2 * C / r + C / r = (12 * X + 33) / r := by dsimp [C]; ring
  rw [he]
  dsimp [X] at hj ⊢
  linarith

end TaoFivePrimes
