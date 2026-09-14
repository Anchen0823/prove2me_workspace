import Mathlib

/-!
The three numerical rows used for the Rosser--Schoenfeld remainder estimate.

The analytic estimates themselves are hypotheses here.  This lemma records the
elementary numerical bridge from those rows to the common bound `y / (40 * t)`.
-/
theorem sondow_schoenfeld_three_rows
    {t y E : ℝ}
    (ht_lower : (18.42 : ℝ) ≤ t)
    (ht_upper : t ≤ 1300)
    (hy : 0 ≤ y)
    (h₁ : t < 20 → E ≤ 0.0012015 * y)
    (h₂ : 20 ≤ t → t < 35 → E ≤ 0.00065941 * y)
    (h₃ : 35 ≤ t → E ≤ 0.000018315 * y) :
    E ≤ y / (40 * t) := by
  have ht_pos : 0 < t := by linarith
  have hden : 0 < 40 * t := by positivity
  rcases lt_or_ge t 20 with ht20 | ht20
  · have hE : E ≤ 0.0012015 * y := h₁ ht20
    have hc : 0.0012015 * (40 * t) ≤ 1 := by
      nlinarith
    have hcy : (0.0012015 * (40 * t)) * y ≤ 1 * y :=
      mul_le_mul_of_nonneg_right hc hy
    apply (le_div_iff₀ hden).2
    calc
      E * (40 * t) ≤ (0.0012015 * y) * (40 * t) :=
        mul_le_mul_of_nonneg_right hE (by positivity)
      _ = (0.0012015 * (40 * t)) * y := by ring
      _ ≤ 1 * y := hcy
      _ = y := by ring
  · rcases lt_or_ge t 35 with ht35 | ht35
    · have hE : E ≤ 0.00065941 * y := h₂ ht20 ht35
      have hc : 0.00065941 * (40 * t) ≤ 1 := by
        nlinarith
      have hcy : (0.00065941 * (40 * t)) * y ≤ 1 * y :=
        mul_le_mul_of_nonneg_right hc hy
      apply (le_div_iff₀ hden).2
      calc
        E * (40 * t) ≤ (0.00065941 * y) * (40 * t) :=
          mul_le_mul_of_nonneg_right hE (by positivity)
        _ = (0.00065941 * (40 * t)) * y := by ring
        _ ≤ 1 * y := hcy
        _ = y := by ring
    · have hE : E ≤ 0.000018315 * y := h₃ ht35
      have hc : 0.000018315 * (40 * t) ≤ 1 := by
        nlinarith
      have hcy : (0.000018315 * (40 * t)) * y ≤ 1 * y :=
        mul_le_mul_of_nonneg_right hc hy
      apply (le_div_iff₀ hden).2
      calc
        E * (40 * t) ≤ (0.000018315 * y) * (40 * t) :=
          mul_le_mul_of_nonneg_right hE (by positivity)
        _ = (0.000018315 * (40 * t)) * y := by ring
        _ ≤ 1 * y := hcy
        _ = y := by ring

#print axioms sondow_schoenfeld_three_rows
