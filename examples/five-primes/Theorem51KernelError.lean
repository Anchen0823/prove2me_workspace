import Mathlib.Tactic

namespace TaoFivePrimes
open Finset

/-- A bounded off-diagonal kernel costs at most one unit per other index. -/
theorem bounded_kernel_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → ι → ℂ) (hE : ∀ m n, m ≠ n → ‖E m n‖ ≤ 1) (x : ι → ℂ) :
    ‖∑ m, ∑ n ∈ univ.erase m, star (x m) * E m n * x n‖ ≤
      ((Fintype.card ι : ℝ) - 1) * ∑ m, ‖x m‖ ^ 2 := by
  have hp (m n : ι) (hn : n ∈ univ.erase m) :
      ‖star (x m) * E m n * x n‖ ≤ (‖x m‖ ^ 2 + ‖x n‖ ^ 2) / 2 := by
    rw [norm_mul, norm_mul, norm_star]
    have he := hE m n (Ne.symm (mem_erase.mp hn).1)
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he (norm_nonneg (x m))) (norm_nonneg (x n))
    nlinarith [sq_nonneg (‖x m‖ - ‖x n‖)]
  have hcard (m : ι) : ((univ.erase m).card : ℝ) = (Fintype.card ι : ℝ) - 1 := by
    have hh := Finset.card_erase_add_one (s := (univ : Finset ι)) (mem_univ m)
    have hh' : ((univ.erase m).card : ℝ) + 1 = (Fintype.card ι : ℝ) := by
      exact_mod_cast hh
    linarith
  have hs : (∑ m, ∑ n ∈ univ.erase m, ‖x n‖ ^ 2) =
      ((Fintype.card ι : ℝ) - 1) * ∑ m, ‖x m‖ ^ 2 := by
    rw [Finset.sum_comm' (t' := univ) (s' := fun n => univ.erase n)]
    · simp only [sum_const, nsmul_eq_mul, hcard, ← mul_sum]
    · intro n m
      simp only [mem_univ, mem_erase, true_and, and_true]
      exact ⟨Ne.symm, Ne.symm⟩
  calc
    _ ≤ ∑ m, ∑ n ∈ univ.erase m, ‖star (x m) * E m n * x n‖ := by
      exact (norm_sum_le _ _).trans (sum_le_sum fun m hm => norm_sum_le _ _)
    _ ≤ ∑ m, ∑ n ∈ univ.erase m, (‖x m‖ ^ 2 + ‖x n‖ ^ 2) / 2 := by
      exact sum_le_sum fun m hm => sum_le_sum fun n hn => hp m n hn
    _ = _ := by
      simp only [← Finset.sum_div, Finset.sum_add_distrib, sum_const, nsmul_eq_mul]
      rw [hs]
      simp only [hcard, ← mul_sum]
      ring

end TaoFivePrimes
