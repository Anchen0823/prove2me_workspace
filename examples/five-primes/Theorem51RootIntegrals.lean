import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace TaoFivePrimes
open MeasureTheory

lemma integral_inv_sqrt_positive (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, 1 / Real.sqrt t) = 2 * (Real.sqrt b - Real.sqrt a) := by
  have hp : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht => ha.trans_le ht.1
  have hc : ContinuousOn (fun t : ℝ => 1 / Real.sqrt t) (Set.Icc a b) :=
    continuousOn_const.div Real.continuous_sqrt.continuousOn
      (fun t ht => (Real.sqrt_pos.mpr (hp t ht)).ne')
  have hi : IntervalIntegrable (fun t : ℝ => 1 / Real.sqrt t) volume a b :=
    hc.intervalIntegrable_of_Icc hab
  have hd : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => 2 * Real.sqrt t) (1 / Real.sqrt t) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    convert (Real.hasDerivAt_sqrt (hp t ht).ne').const_mul 2 using 1 <;> first | rfl | ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  convert he using 1 <;> first | rfl | ring

lemma integral_inv_mul_sqrt_positive (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, 1 / (t * Real.sqrt t)) = 2 / Real.sqrt a - 2 / Real.sqrt b := by
  have hp : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht => ha.trans_le ht.1
  have hc : ContinuousOn (fun t : ℝ => 1 / (t * Real.sqrt t)) (Set.Icc a b) :=
    continuousOn_const.div (continuousOn_id.mul Real.continuous_sqrt.continuousOn)
      (fun t ht => (mul_pos (hp t ht) (Real.sqrt_pos.mpr (hp t ht))).ne')
  have hi : IntervalIntegrable (fun t : ℝ => 1 / (t * Real.sqrt t)) volume a b :=
    hc.intervalIntegrable_of_Icc hab
  have hd : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => -2 / Real.sqrt t) (1 / (t * Real.sqrt t)) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 := hp t ht
    have hs0 : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht0).ne'
    convert ((Real.hasDerivAt_sqrt ht0.ne').inv hs0).const_mul (-2) using 1 <;>
      first | rfl | (field_simp; nlinarith [Real.sq_sqrt ht0.le])
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  convert he using 1 <;> first | rfl | ring

lemma integral_log_weight_le (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) (hn : ∀ t ∈ Set.Icc a b, 0 ≤ f t) :
    (∫ t in a..b, Real.log t * f t) ≤ Real.log b * ∫ t in a..b, f t := by
  have hp : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht => ha.trans_le ht.1
  have hl : ContinuousOn Real.log (Set.Icc a b) :=
    continuousOn_id.log (fun t ht => (hp t ht).ne')
  have hi : IntervalIntegrable (fun t => Real.log t * f t) volume a b :=
    (hl.mul hf).intervalIntegrable_of_Icc hab
  have hj : IntervalIntegrable (fun t => Real.log b * f t) volume a b :=
    (continuousOn_const.mul hf).intervalIntegrable_of_Icc hab
  have hm := intervalIntegral.integral_mono_on hab hi hj (fun t ht =>
    mul_le_mul_of_nonneg_right (Real.log_le_log (hp t ht) ht.2) (hn t ht))
  rwa [intervalIntegral.integral_const_mul] at hm

lemma integral_log_inv_sqrt_le (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, Real.log t * (1 / Real.sqrt t)) ≤
      2 * Real.sqrt b * Real.log b := by
  have ha0 : 0 < a := by linarith
  have hp : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht => ha0.trans_le ht.1
  have hc : ContinuousOn (fun t : ℝ => 1 / Real.sqrt t) (Set.Icc a b) :=
    continuousOn_const.div Real.continuous_sqrt.continuousOn
      (fun t ht => (Real.sqrt_pos.mpr (hp t ht)).ne')
  have hm := integral_log_weight_le a b ha0 hab _ hc (fun t ht => by positivity)
  rw [integral_inv_sqrt_positive a b ha0 hab] at hm
  have hl := Real.log_nonneg (ha.trans hab)
  nlinarith [mul_nonneg (Real.sqrt_nonneg a) hl]

lemma integral_log_inv_mul_sqrt_le (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, Real.log t * (1 / (t * Real.sqrt t))) ≤
      (2 / Real.sqrt a) * Real.log b := by
  have ha0 : 0 < a := by linarith
  have hp : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht => ha0.trans_le ht.1
  have hc : ContinuousOn (fun t : ℝ => 1 / (t * Real.sqrt t)) (Set.Icc a b) :=
    continuousOn_const.div (continuousOn_id.mul Real.continuous_sqrt.continuousOn)
      (fun t ht => (mul_pos (hp t ht) (Real.sqrt_pos.mpr (hp t ht))).ne')
  have hm := integral_log_weight_le a b ha0 hab _ hc (fun t ht =>
    div_nonneg (by norm_num) (mul_nonneg (hp t ht).le (Real.sqrt_nonneg t)))
  rw [integral_inv_mul_sqrt_positive a b ha0 hab] at hm
  have hl := Real.log_nonneg (ha.trans hab)
  nlinarith [mul_nonneg (show 0 ≤ 2 / Real.sqrt b by positivity) hl]

end TaoFivePrimes

