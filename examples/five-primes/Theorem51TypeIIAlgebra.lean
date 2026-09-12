import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace TaoFivePrimes

/-- A coupled radical estimate. The last two terms cannot be obtained by
termwise subadditivity alone; the hypothesis supplies the missing cross term. -/
lemma sqrt_four_terms_coupled (A B C D : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hCD : C ≤ 8 * D) :
    Real.sqrt (A + B + C + D) ≤
      Real.sqrt A + Real.sqrt B + Real.sqrt (C / 2) + Real.sqrt D := by
  have hsmall : Real.sqrt (C / 2) ≤ 2 * Real.sqrt D := by
    apply (Real.sqrt_le_left (by positivity)).2
    nlinarith [Real.sq_sqrt hD]
  have hcross := mul_nonneg (Real.sqrt_nonneg (C / 2)) (sub_nonneg.mpr hsmall)
  have hrest := mul_nonneg
    (show 0 ≤ Real.sqrt A + Real.sqrt B by positivity)
    (show 0 ≤ Real.sqrt (C / 2) + Real.sqrt D by positivity)
  apply (Real.sqrt_le_left (by positivity)).2
  nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB,
    Real.sq_sqrt (show 0 ≤ C / 2 by positivity), Real.sq_sqrt hD,
    mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B)]

/-- The unit-numerator parameter regime couples the Type II scales. -/
lemma unit_regime_x_le_q_mul_W (x U V q W : ℝ)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hUV : U * V < q - 1)
    (hx : x ≤ U * V ^ 2) (hW : V ≤ W) : x ≤ q * W := by
  have hq : 0 ≤ q := by nlinarith [mul_nonneg hU hV]
  have h1 : U * V ^ 2 ≤ q * V := by nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_lt hUV)) hV]
  have h2 : q * V ≤ q * W := mul_le_mul_of_nonneg_left hW hq
  exact hx.trans (h1.trans h2)

/-- Algebra behind the pointwise Type II bound, valid in the unit regime. -/
lemma typeII_radical_unit (x q W : ℝ) (hx : 0 < x) (hq : 0 < q)
    (hW : 0 < W) (hxqW : x ≤ q * W) :
    Real.sqrt ((W / 4 + 2 * q) * (x / (2 * W * q) + 1) * x) ≤
      Real.sqrt (x ^ 2 / (8 * q)) + Real.sqrt (x * W / 4) +
        Real.sqrt (x ^ 2 / (2 * W)) + Real.sqrt (2 * q * x) := by
  have he : (W / 4 + 2 * q) * (x / (2 * W * q) + 1) * x =
      x ^ 2 / (8 * q) + x * W / 4 + x ^ 2 / W + 2 * q * x := by
    field_simp
    <;> ring
  have hc : x ^ 2 / W ≤ 8 * (2 * q * x) := by
    apply (div_le_iff₀ hW).2
    have hm := mul_le_mul_of_nonneg_left hxqW hx.le
    nlinarith [mul_pos hq hx, mul_pos (mul_pos hq hx) hW]
  rw [he]
  simpa only [div_div, mul_comm W 2] using sqrt_four_terms_coupled (x ^ 2 / (8 * q)) (x * W / 4)
    (x ^ 2 / W) (2 * q * x) (by positivity) (by positivity)
    (by positivity) (by positivity) hc

/-- Rounding the exact radical constants to the constants of Theorem 5.1. -/
lemma typeII_round_constants (A B C D L M : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (_hC : 0 ≤ C) (hD : 0 ≤ D)
    (hL : 0 ≤ L) (hM : 0 ≤ M) :
    (1.1 / 4) * (1 / (2 * Real.sqrt 2) * A + Real.sqrt 2 * B) * L +
      1.1 * ((1 / 2) * C + (1 / Real.sqrt 2) * D) * M ≤
    (0.1 * A + 0.39 * B) * L + (0.55 * C + 0.78 * D) * M := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hsl : (1.414 : ℝ) ≤ Real.sqrt 2 := by nlinarith
  have hsu : Real.sqrt 2 ≤ (1.415 : ℝ) := by nlinarith
  have hp : 0 < Real.sqrt 2 := by positivity
  have hc1 : (1.1 / 4 : ℝ) * (1 / (2 * Real.sqrt 2)) ≤ 0.1 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  have hc2 : (1.1 / 4 : ℝ) * Real.sqrt 2 ≤ 0.39 := by linarith
  have hc3 : (1.1 : ℝ) * (1 / Real.sqrt 2) ≤ 0.78 := by
    rw [mul_one_div, div_le_iff₀ hp]
    linarith
  calc
    _ = ((1.1 / 4) * (1 / (2 * Real.sqrt 2)) * A +
        ((1.1 / 4) * Real.sqrt 2) * B) * L +
        (0.55 * C + (1.1 * (1 / Real.sqrt 2)) * D) * M := by ring
    _ ≤ _ := by gcongr

end TaoFivePrimes
