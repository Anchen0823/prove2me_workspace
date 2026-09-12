import examples.«five-primes».CutoffEnergy
import Mathlib.NumberTheory.Chebyshev

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

/-- A weight vanishing below the sifting threshold loses only nonprime mass. -/
theorem weighted_sieve_loss_le (x : ℕ) (w : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (hzero : ∀ n, n ≤ Nat.sqrt x → w n = 0) :
    |(∑ n ∈ Finset.range (x + 1), siftedVonMangoldt x n * w n) -
      (∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) * w n)| ≤
      Chebyshev.psi x - Chebyshev.theta x := by
  have hp (n : ℕ) :
      0 ≤ ((Λ n : ℝ) - siftedVonMangoldt x n) * w n ∧
      ((Λ n : ℝ) - siftedVonMangoldt x n) * w n ≤
        if n.Prime then 0 else (Λ n : ℝ) := by
    unfold siftedVonMangoldt
    by_cases hc : n.Coprime (primorial (Nat.sqrt x))
    · simp only [if_pos hc, sub_self, zero_mul]
      constructor
      · exact le_rfl
      · split_ifs <;> positivity
    · simp only [if_neg hc, sub_zero]
      constructor
      · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hw n).1
      · by_cases hn : n.Prime
        · have hsmall : n ≤ Nat.sqrt x := by
            apply hn.dvd_primorial_iff.mp
            exact not_not.mp ((hn.coprime_iff_not_dvd).not.mp hc)
          simp [hn, hzero n hsmall]
        · simp only [hn, if_false]
          exact (mul_le_mul_of_nonneg_left (hw n).2
            ArithmeticFunction.vonMangoldt_nonneg).trans_eq (mul_one _)
  have hnonneg : 0 ≤ ∑ n ∈ Finset.range (x + 1),
      ((Λ n : ℝ) - siftedVonMangoldt x n) * w n :=
    Finset.sum_nonneg (fun n _ => (hp n).1)
  have heq : (∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) * w n) -
      (∑ n ∈ Finset.range (x + 1), siftedVonMangoldt x n * w n) =
      ∑ n ∈ Finset.range (x + 1), ((Λ n : ℝ) - siftedVonMangoldt x n) * w n := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [sub_mul]
  rw [abs_sub_comm, heq, abs_of_nonneg hnonneg]
  apply (Finset.sum_le_sum (fun n _ => (hp n).2)).trans_eq
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, Finset.sum_filter]
  have hs : Finset.range (x + 1) = insert 0 (Finset.Ioc 0 x) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [hs, Finset.sum_insert (by simp)]
  simp

end TaoFivePrimes
