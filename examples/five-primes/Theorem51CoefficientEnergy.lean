import Definitions.Def_TaoFivePrimes_Theorem51Sums
import Mathlib.Tactic

namespace TaoFivePrimes
open Finset

/-- The half-log bound for the exact coefficient in the public Type II sum. -/
theorem theorem51Centered_abs_le (V : ℝ) (w : ℕ) :
    |theorem51Centered V w| ≤ Real.log w / 2 := by
  have hlo : 0 ≤ ∑ b ∈ w.divisors.filter (fun b : ℕ => V < (b : ℝ)),
      ArithmeticFunction.vonMangoldt b :=
    sum_nonneg fun b hb => ArithmeticFunction.vonMangoldt_nonneg
  have hhi : (∑ b ∈ w.divisors.filter (fun b : ℕ => V < (b : ℝ)),
      ArithmeticFunction.vonMangoldt b) ≤ Real.log w := by
    rw [← ArithmeticFunction.vonMangoldt_sum]
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro b hb hb'
    exact ArithmeticFunction.vonMangoldt_nonneg
  unfold theorem51Centered
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem theorem51Centered_energy (s : Finset ℕ) (V W : ℝ) (hW : 1 ≤ W)
    (hs : ∀ w ∈ s, 0 < w ∧ (w : ℝ) ≤ W) :
    (∑ w ∈ s, ‖(theorem51Centered V w : ℂ)‖ ^ 2) ≤
      (s.card : ℝ) * (Real.log W / 2) ^ 2 := by
  calc
    _ ≤ ∑ w ∈ s, (Real.log W / 2) ^ 2 := by
      apply sum_le_sum
      intro w hw
      apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg (Real.log_nonneg hW) (by norm_num))).mpr
      rw [Complex.norm_real, Real.norm_eq_abs]
      have hh := theorem51Centered_abs_le V w
      have hl := Real.log_le_log (by exact_mod_cast (hs w hw).1) (hs w hw).2
      linarith
    _ = _ := by simp only [sum_const, nsmul_eq_mul]

theorem moebius_coefficient_energy (s : Finset ℕ) :
    (∑ d ∈ s, ‖(ArithmeticFunction.moebius d : ℂ)‖ ^ 2) ≤ (s.card : ℝ) := by
  calc
    _ ≤ ∑ d ∈ s, (1 : ℝ) := by
      apply sum_le_sum
      intro d hd
      have h : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
      nlinarith [norm_nonneg (ArithmeticFunction.moebius d : ℂ)]
    _ = _ := by simp

end TaoFivePrimes
