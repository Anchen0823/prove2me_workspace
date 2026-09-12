import examples.«five-primes».Theorem51CutoffAmplitude
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace TaoFivePrimes
open MeasureTheory

/-- The cutoff is the logarithmic length of the overlap of two scale windows. -/
lemma eta0_log_overlap (r w : ℝ) (hr : 0 < r) (hw : 0 < w) :
    eta0 (w / r) =
      if max w (r / 2) < min (2 * w) r then
        4 * Real.log (min (2 * w) r / max w (r / 2)) else 0 := by
  by_cases hlow : w ≤ r / 4
  · rw [eta0_zero_below_quarter ((div_le_iff₀ hr).mpr (by linarith))]
    have hh : ¬ max w (r / 2) < min (2 * w) r := by
      have h1 := le_max_right w (r / 2)
      have h2 := min_le_left (2 * w) r
      linarith
    rw [if_neg hh]
  · by_cases hmid : w ≤ r / 2
    · have htlo : 1 / 4 ≤ w / r := (le_div_iff₀ hr).mpr (by linarith)
      have hthi : w / r ≤ 1 / 2 := (div_le_iff₀ hr).mpr (by linarith)
      rw [eta0_lower_piece htlo hthi, max_eq_right hmid,
        min_eq_left (by linarith : 2 * w ≤ r), if_pos (by linarith)]
      congr 2
      ring
    · by_cases hhigh : w < r
      · have htlo : 1 / 2 ≤ w / r := (le_div_iff₀ hr).mpr (by linarith)
        have hthi : w / r ≤ 1 := (div_le_iff₀ hr).mpr (by linarith)
        rw [eta0_upper_piece htlo hthi, max_eq_left (by linarith : r / 2 ≤ w),
          min_eq_right (by linarith : r ≤ 2 * w), if_pos hhigh,
          Real.log_div hr.ne' hw.ne', Real.log_div hw.ne' hr.ne']
        ring
      · rw [eta0_zero_above_one ((le_div_iff₀ hr).mpr (by linarith))]
        have hh : ¬ max w (r / 2) < min (2 * w) r := by
          have h1 := le_max_left w (r / 2)
          have h2 := min_le_right (2 * w) r
          linarith
        rw [if_neg hh]

lemma integral_inv_Icc_positive (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ t in Set.Icc a b, (t : ℝ)⁻¹) = if a < b then Real.log (b / a) else 0 := by
  by_cases hab : a < b
  · rw [if_pos hab, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab.le, integral_inv_of_pos ha hb]
  · rw [if_neg hab]
    rcases lt_or_eq_of_le (le_of_not_gt hab) with hba | rfl
    · simp [Set.Icc_eq_empty_of_lt hba]
    · simp

lemma eta0_scale_integral (r w : ℝ) (hr : 0 < r) (hw : 0 < w) :
    eta0 (w / r) =
      4 * ∫ W in Set.Icc (max w (r / 2)) (min (2 * w) r), (W : ℝ)⁻¹ := by
  rw [integral_inv_Icc_positive _ _ (lt_of_lt_of_le hw (le_max_left _ _))
    (lt_min (by positivity) hr), eta0_log_overlap r w hr hw]
  split_ifs <;> simp

lemma scale_pair_mem (x d w W : ℝ) (hd : 0 < d) (hw : 0 < w) :
    (x / (2 * W) ≤ d ∧ d ≤ x / W ∧ W / 2 ≤ w ∧ w ≤ W) ↔
      W ∈ Set.Icc (max w (x / d / 2)) (min (2 * w) (x / d)) := by
  simp only [Set.mem_Icc, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hW : 0 < W := hw.trans_le h4
    have ha := (div_le_iff₀ (show 0 < 2 * W by positivity)).mp h1
    have hb := (le_div_iff₀ hW).mp h2
    refine ⟨⟨h4, ?_⟩, ⟨by linarith, ?_⟩⟩
    · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      apply (div_le_iff₀ hd).mpr
      nlinarith
    · apply (le_div_iff₀ hd).mpr
      nlinarith
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    have hW : 0 < W := hw.trans_le h1
    have ha := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp h2
    have hb := (div_le_iff₀ hd).mp ha
    have hc := (le_div_iff₀ hd).mp h4
    refine ⟨?_, ?_, by linarith, h1⟩
    · apply (div_le_iff₀ (show 0 < 2 * W by positivity)).mpr
      nlinarith
    · apply (le_div_iff₀ hW).mpr
      nlinarith

/-- A single actual (d,w) summand has precisely the required scale integral. -/
lemma eta0_pair_scale_integral (x d w : ℝ) (hx : 0 < x) (hd : 0 < d) (hw : 0 < w) :
    eta0 (d * w / x) = 4 * ∫ W : ℝ,
      if x / (2 * W) ≤ d ∧ d ≤ x / W ∧ W / 2 ≤ w ∧ w ≤ W then W⁻¹ else 0 := by
  have he : (fun W : ℝ =>
      if x / (2 * W) ≤ d ∧ d ≤ x / W ∧ W / 2 ≤ w ∧ w ≤ W then W⁻¹ else 0) =
      (Set.Icc (max w (x / d / 2)) (min (2 * w) (x / d))).indicator (fun W : ℝ => W⁻¹) := by
    funext W
    simp only [Set.indicator, scale_pair_mem x d w W hd hw]
  rw [he, integral_indicator measurableSet_Icc]
  have hh := eta0_scale_integral (x / d) w (div_pos hx hd) hw
  have ht : w / (x / d) = d * w / x := by field_simp <;> ring
  rwa [ht] at hh

lemma scale_pair_integrable (x d w : ℝ) (hd : 0 < d) (hw : 0 < w) :
    Integrable (fun W : ℝ =>
      if x / (2 * W) ≤ d ∧ d ≤ x / W ∧ W / 2 ≤ w ∧ w ≤ W then W⁻¹ else 0) := by
  have he : (fun W : ℝ =>
      if x / (2 * W) ≤ d ∧ d ≤ x / W ∧ W / 2 ≤ w ∧ w ≤ W then W⁻¹ else 0) =
      (Set.Icc (max w (x / d / 2)) (min (2 * w) (x / d))).indicator (fun W : ℝ => W⁻¹) := by
    funext W
    simp only [Set.indicator, scale_pair_mem x d w W hd hw]
  rw [he, integrable_indicator_iff measurableSet_Icc]
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  apply continuousOn_id.inv₀
  intro W hW
  exact (hw.trans_le ((le_max_left _ _).trans hW.1)).ne'

lemma eta0_pair_scale_integral_complex (x d w : ℝ) (c : ℂ)
    (hx : 0 < x) (hd : 0 < d) (hw : 0 < w) :
    c * (eta0 (d * w / x) : ℂ) = 4 * ∫ W : ℝ, c *
      ((if x / (2 * W) ≤ d ∧ d ≤ x / W ∧ W / 2 ≤ w ∧ w ≤ W then W⁻¹ else 0 : ℝ) : ℂ) := by
  rw [integral_const_mul, integral_complex_ofReal, eta0_pair_scale_integral x d w hx hd hw]
  push_cast
  ring

/-- Finite-sum/interchange version of the actual pairwise scale decomposition. -/
lemma finite_eta0_scale_integral {ι : Type*} (s : Finset ι) (x : ℝ)
    (d w : ι → ℝ) (c : ι → ℂ) (hx : 0 < x)
    (hd : ∀ i ∈ s, 0 < d i) (hw : ∀ i ∈ s, 0 < w i) :
    (∑ i ∈ s, c i * (eta0 (d i * w i / x) : ℂ)) =
      4 * ∫ W : ℝ, ∑ i ∈ s, c i *
        ((if x / (2 * W) ≤ d i ∧ d i ≤ x / W ∧ W / 2 ≤ w i ∧ w i ≤ W
          then W⁻¹ else 0 : ℝ) : ℂ) := by
  let F (i : ι) (W : ℝ) : ℂ := c i *
    ((if x / (2 * W) ≤ d i ∧ d i ≤ x / W ∧ W / 2 ≤ w i ∧ w i ≤ W
      then W⁻¹ else 0 : ℝ) : ℂ)
  have hint (i : ι) (hi : i ∈ s) : Integrable (F i) :=
    ((scale_pair_integrable x (d i) (w i) (hd i hi) (hw i hi)).ofReal).const_mul (c i)
  calc
    _ = ∑ i ∈ s, (4 : ℂ) * ∫ W, F i W := by
      apply Finset.sum_congr rfl
      intro i hi
      exact eta0_pair_scale_integral_complex x (d i) (w i) (c i) hx (hd i hi) (hw i hi)
    _ = 4 * ∑ i ∈ s, ∫ W, F i W := (Finset.mul_sum s _ 4).symm
    _ = _ := by
      congr 1
      exact (integral_finsetSum s hint).symm

end TaoFivePrimes

