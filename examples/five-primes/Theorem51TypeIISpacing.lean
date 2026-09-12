import examples.«five-primes».Theorem51PhaseAudit

namespace TaoFivePrimes

/-- The unit numerator gives nearly 1/q spacing, stronger than 1/(2q). -/
lemma unit_half_block_window (alpha beta q j : ℝ) (hq : 4 ≤ q)
    (hj : 1 ≤ j) (hjq : j ≤ q / 2)
    (hphase : 4 * alpha = 1 / q + beta) (hbeta : |beta| ≤ 1 / q ^ 2) :
    (q - 1) / q ^ 2 ≤ 4 * j * alpha ∧
      4 * j * alpha ≤ 1 - (q - 1) / q ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hqm : 0 ≤ q - 1 := by linarith
  have hδ : 0 ≤ (q - 1) / q ^ 2 := by positivity
  have hw := unit_phase_window alpha beta q hq0 hphase hbeta
  have hlo : (q - 1) / q ^ 2 ≤ 4 * alpha := by
    have he : (q - 1) / (4 * q ^ 2) = ((q - 1) / q ^ 2) / 4 := by ring
    rw [he] at hw
    linarith [hw.1]
  have hhi : 4 * alpha ≤ (q + 1) / q ^ 2 := by
    have he : (q + 1) / (4 * q ^ 2) = ((q + 1) / q ^ 2) / 4 := by ring
    rw [he] at hw
    linarith [hw.2]
  have hα : 0 ≤ 4 * alpha := hδ.trans hlo
  constructor
  · have h1 := mul_le_mul_of_nonneg_left hlo (by linarith : 0 ≤ j)
    have h2 := mul_le_mul_of_nonneg_right hj hδ
    nlinarith
  · have h1 := mul_le_mul_of_nonneg_left hhi (by linarith : 0 ≤ j)
    have h2 := mul_le_mul_of_nonneg_right hjq (show 0 ≤ (q + 1) / q ^ 2 by positivity)
    have h3 : q / 2 * ((q + 1) / q ^ 2) ≤ 1 - (q - 1) / q ^ 2 := by
      field_simp
      nlinarith [sq_nonneg (q - 2)]
    nlinarith

lemma unit_half_block_spacing (alpha beta q j : ℝ) (hq : 4 ≤ q)
    (hj : 1 ≤ j) (hjq : j ≤ q / 2)
    (hphase : 4 * alpha = 1 / q + beta) (hbeta : |beta| ≤ 1 / q ^ 2) (k : ℤ) :
    (q - 1) / q ^ 2 ≤ |4 * j * alpha - (k : ℝ)| := by
  have hw := unit_half_block_window alpha beta q j hq hj hjq hphase hbeta
  by_cases hk : k ≤ 0
  · have hkR : (k : ℝ) ≤ 0 := by exact_mod_cast hk
    linarith [le_abs_self (4 * j * alpha - (k : ℝ))]
  · have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    linarith [neg_le_abs (4 * j * alpha - (k : ℝ))]

end TaoFivePrimes
