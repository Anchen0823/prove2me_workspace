import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace TaoFivePrimes

/-- Exact phase bounds for the positive unit numerator. -/
lemma unit_phase_window (alpha beta q : ℝ) (hq : 0 < q)
    (hphase : 4 * alpha = 1 / q + beta) (hbeta : |beta| ≤ 1 / q ^ 2) :
    (q - 1) / (4 * q ^ 2) ≤ alpha ∧ alpha ≤ (q + 1) / (4 * q ^ 2) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hbeta
  have helo : (q - 1) / (4 * q ^ 2) = (1 / q - 1 / q ^ 2) / 4 := by
    field_simp
    <;> ring
  have hehi : (q + 1) / (4 * q ^ 2) = (1 / q + 1 / q ^ 2) / 4 := by
    field_simp
    <;> ring
  rw [helo, hehi]
  constructor <;> linarith

/-- The reversed sine comparison in the paragraph preceding (5.18)
cannot be used verbatim, even with beta = 0 and q = 1602. This is a
counterexample to that intermediate comparison, not to Theorem 5.1. -/
lemma source_typeI_sine_comparison_fails :
    ¬ (Real.sin (2 * Real.pi * (1 : ℝ) * (1 / (4 * 1602))) ≥
      Real.sin (2 * Real.pi * (1 : ℝ) / (4 * (1602 - 1)))) := by
  have hs : Real.sin (Real.pi / 3204) < Real.sin (Real.pi / 3202) := by
    apply Real.sin_lt_sin_of_lt_of_le_pi_div_two <;> linarith [Real.pi_pos]
  have he1 : 2 * Real.pi * (1 : ℝ) * (1 / (4 * 1602)) = Real.pi / 3204 := by ring
  have he2 : 2 * Real.pi * (1 : ℝ) / (4 * (1602 - 1)) = Real.pi / 3202 := by ring
  rw [he1, he2]
  exact not_le_of_gt hs

/-- The numerical parameters in the preceding comparison are in the
actual unit-numerator parameter regime. -/
lemma source_typeI_counterexample_parameters :
    (40 : ℝ) * 40 ≤ 6400 / 4 ∧
    (6400 : ℝ) ≤ 40 * 40 ^ 2 ∧
    (40 : ℝ) * 40 < 1602 - 1 ∧
    (40 : ℝ) < 6400 ∧
    4 * (1 / (4 * 1602) : ℝ) = 1 / 1602 + 0 ∧
    |(0 : ℝ)| ≤ 1 / (1602 : ℝ) ^ 2 := by norm_num

/-- A valid lower sine envelope, keeping the exact lower endpoint of the
phase window instead of substituting its upper endpoint. -/
lemma unit_phase_sine_lower (alpha beta q d : ℝ) (hq : 1 < q)
    (hd : 0 ≤ d) (hdq : d ≤ q - 1)
    (hphase : 4 * alpha = 1 / q + beta) (hbeta : |beta| ≤ 1 / q ^ 2) :
    Real.sin (2 * Real.pi * d * ((q - 1) / (4 * q ^ 2))) ≤
      Real.sin (2 * Real.pi * d * alpha) := by
  have hq0 : 0 < q := by linarith
  obtain ⟨hlo, hhi⟩ := unit_phase_window alpha beta q hq0 hphase hbeta
  have hqm : 0 < q - 1 := by linarith
  have ha : 0 ≤ alpha := le_trans (by positivity) hlo
  have hupper : alpha ≤ 1 / (4 * (q - 1)) := by
    apply hhi.trans
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  have hdalpha : d * alpha ≤ 1 / 4 := by
    calc
      _ ≤ (q - 1) * alpha := mul_le_mul_of_nonneg_right hdq ha
      _ ≤ (q - 1) * (1 / (4 * (q - 1))) :=
        mul_le_mul_of_nonneg_left hupper hqm.le
      _ = 1 / 4 := by field_simp
  apply Real.sin_le_sin_of_le_of_le_pi_div_two
  · have hnonneg : 0 ≤ 2 * Real.pi * d * ((q - 1) / (4 * q ^ 2)) := by positivity
    linarith [Real.pi_pos]
  · have hm := mul_le_mul_of_nonneg_left hdalpha (show 0 ≤ 2 * Real.pi by positivity)
    nlinarith
  · exact mul_le_mul_of_nonneg_left hlo (by positivity)

end TaoFivePrimes
