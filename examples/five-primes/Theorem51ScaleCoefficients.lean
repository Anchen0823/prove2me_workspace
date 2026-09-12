import Definitions.Def_TaoFivePrimes_Theorem51Scale
import examples.«five-primes».Theorem51ScaleIntervals
import examples.«five-primes».Theorem51CoefficientEnergy

namespace TaoFivePrimes
open Finset

lemma scale_column_energy (s : Finset ℤ) (U : ℝ) :
    (∑ n ∈ s, ‖scaleColumnCoefficient U n‖ ^ 2) ≤ (s.card : ℝ) := by
  calc
    _ ≤ ∑ n ∈ s, (1 : ℝ) := by
      apply sum_le_sum
      intro n hn
      unfold scaleColumnCoefficient
      split_ifs
      · have h : ‖(ArithmeticFunction.moebius (2 * n + 1).toNat : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_intCast]
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := (2 * n + 1).toNat))
        nlinarith [norm_nonneg (ArithmeticFunction.moebius (2 * n + 1).toNat : ℂ)]
      · norm_num
    _ = _ := by simp

lemma scale_row_energy (V W : ℝ) (hW : 40 ≤ W) :
    (∑ w ∈ oddRealInterval (W / 2) W, ‖scaleRowCoefficient V w‖ ^ 2) ≤
      ((oddRealInterval (W / 2) W).card : ℝ) * (Real.log W / 2) ^ 2 := by
  calc
    _ ≤ ∑ w ∈ oddRealInterval (W / 2) W, (Real.log W / 2) ^ 2 := by
      apply sum_le_sum
      intro w hw
      have hh := (mem_oddRealInterval (W / 2) W w).mp hw
      have hw0 : 0 ≤ w := by exact_mod_cast (show (0 : ℝ) ≤ w by linarith)
      have he : (w.toNat : ℝ) = (w : ℝ) := by
        exact_mod_cast (Int.toNat_of_nonneg hw0)
      unfold scaleRowCoefficient
      split_ifs
      · apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg (Real.log_nonneg (by linarith)) (by norm_num))).mpr
        rw [Complex.norm_real, Real.norm_eq_abs]
        have hb := theorem51Centered_abs_le V w.toNat
        have hl : Real.log (w.toNat : ℝ) ≤ Real.log W := by
          apply Real.log_le_log
          · rw [he]; linarith
          · rw [he]; exact hh.2.1
        linarith
      · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        positivity
    _ = _ := by simp only [sum_const, nsmul_eq_mul]

end TaoFivePrimes

