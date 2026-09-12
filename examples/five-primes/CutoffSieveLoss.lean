import examples.«five-primes».SieveLoss
import examples.«five-primes».SieveLossNumeric

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

theorem eta1_zero_below_sqrt (x : ℕ) (hx : 100 ≤ x) (n : ℕ)
    (hn : n ≤ Nat.sqrt x) : eta1 ((n : ℝ) / x) = 0 := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hs : 10 ≤ Nat.sqrt x := Nat.le_sqrt.mpr (by omega)
  have hsq := Nat.sqrt_le' x
  have hnx : 10 * n ≤ x := by nlinarith
  have hreal : 10 * (n : ℝ) ≤ x := by exact_mod_cast hnx
  have ht : (n : ℝ) / x ≤ 1 / 10 := (div_le_iff₀ hxpos).2 (by linarith)
  rw [eta1_left _ (by linarith)]
  exact max_eq_left (by linarith)

theorem quadratic_sieve_loss (x : ℕ) (hx : (10 ^ 9 : ℝ) ≤ x) :
    |(∑ n ∈ Finset.range (x + 1), siftedVonMangoldt x n * eta1 ((n : ℝ) / x) ^ 2) -
      (∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) * eta1 ((n : ℝ) / x) ^ 2)| ≤
      (x : ℝ) / 150 := by
  have hweight (n : ℕ) : 0 ≤ eta1 ((n : ℝ) / x) ^ 2 ∧
      eta1 ((n : ℝ) / x) ^ 2 ≤ 1 := by
    have h := eta1_bounds ((n : ℝ) / x)
    constructor
    · positivity
    · nlinarith
  have hzero (n : ℕ) (hn : n ≤ Nat.sqrt x) : eta1 ((n : ℝ) / x) ^ 2 = 0 := by
    rw [eta1_zero_below_sqrt x (by exact_mod_cast (show (100 : ℝ) ≤ x by linarith)) n hn]
    norm_num
  calc
    _ ≤ Chebyshev.psi x - Chebyshev.theta x := weighted_sieve_loss_le x _ hweight hzero
    _ ≤ 2 * Real.sqrt x * Real.log x :=
      (le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith))
    _ ≤ _ := sieve_log_error_budget (x : ℝ) hx

end TaoFivePrimes
