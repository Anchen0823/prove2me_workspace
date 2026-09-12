import examples.«five-primes».CutoffEnergy
import examples.«five-primes».CutoffSieveLoss

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

/-- The explicit errors from Tao's Lemmas 4.1 and 4.3 fit the two-percent budget. -/
theorem quadratic_mass_error_budget (x L : ℝ) (hx : 10 ^ 9 ≤ x)
    (hL : 15 / 2 ≤ L) :
    x / (20 * L) + 2.52 * Real.sqrt x ≤ x / 75 := by
  have hx0 : 0 ≤ x := by linarith
  have hs := Real.sq_sqrt hx0
  have hs0 := Real.sqrt_nonneg x
  have hslo : 378 ≤ Real.sqrt x := by nlinarith
  have hfirst : x / (20 * L) ≤ x / 150 := by
    apply (div_le_iff₀ (by linarith : 0 < 20 * L)).2
    nlinarith [mul_nonneg hx0 (show 0 ≤ L - 15 / 2 by linarith)]
  have hsecond : 2.52 * Real.sqrt x ≤ x / 150 := by
    nlinarith [mul_nonneg hs0 (show 0 ≤ Real.sqrt x - 378 by linarith)]
  linarith

/-- Normalize a checked absolute mass error into the exact existential target. -/
theorem quadratic_mass_normalize (x M : ℝ) (hx : 0 < x)
    (hM : |M - (2 / 3) * x| ≤ x / 75) :
    ∃ ε : ℝ, |ε| ≤ 0.02 ∧ M = (2 / 3) * (1 + ε) * x := by
  refine ⟨(M - (2 / 3) * x) / ((2 / 3) * x), ?_, ?_⟩
  · rw [abs_div, abs_of_pos (by positivity : 0 < (2 / 3 : ℝ) * x)]
    apply (div_le_iff₀ (by positivity : 0 < (2 / 3 : ℝ) * x)).2
    linarith
  · field_simp
    <;> ring

/-- The quadratic mass target reduces to an unsifted estimate and the sieve loss. -/
theorem quadratic_prime_mass_of_estimates (x : ℕ)
    (hx : (10 ^ 9 : ℝ) ≤ x) (hlog : 15 / 2 ≤ Real.log ((x : ℝ) / 10))
    (hmain : |(∑ n ∈ Finset.range (x + 1),
        (Λ n : ℝ) * eta1 ((n : ℝ) / x) ^ 2) - (2 / 3 : ℝ) * x| ≤
        (x : ℝ) / (20 * Real.log ((x : ℝ) / 10)))
    (hsieve : |(∑ n ∈ Finset.range (x + 1),
        siftedVonMangoldt x n * eta1 ((n : ℝ) / x) ^ 2) -
        (∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) * eta1 ((n : ℝ) / x) ^ 2)| ≤
        2.52 * Real.sqrt x) :
    ∃ ε : ℝ, |ε| ≤ 0.02 ∧
      (∑ n ∈ Finset.range (x + 1),
        siftedVonMangoldt x n * eta1 ((n : ℝ) / x) ^ 2) =
        (2 / 3 : ℝ) * (1 + ε) * x := by
  apply quadratic_mass_normalize (x : ℝ) _ (by linarith)
  have h := abs_sub_le
    (∑ n ∈ Finset.range (x + 1), siftedVonMangoldt x n * eta1 ((n : ℝ) / x) ^ 2)
    (∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) * eta1 ((n : ℝ) / x) ^ 2)
    ((2 / 3 : ℝ) * x)
  have hb := quadratic_mass_error_budget (x : ℝ) (Real.log ((x : ℝ) / 10)) hx hlog
  linarith

/-- The sieve loss is proved; only the unsifted weighted estimate is assumed. -/
theorem quadratic_prime_mass_of_unsifted (x : ℕ)
    (hx : (10 ^ 9 : ℝ) ≤ x) (hlog : 15 / 2 ≤ Real.log ((x : ℝ) / 10))
    (hmain : |(∑ n ∈ Finset.range (x + 1),
        (Λ n : ℝ) * eta1 ((n : ℝ) / x) ^ 2) - (2 / 3 : ℝ) * x| ≤
        (x : ℝ) / (20 * Real.log ((x : ℝ) / 10))) :
    ∃ ε : ℝ, |ε| ≤ 0.02 ∧
      (∑ n ∈ Finset.range (x + 1),
        siftedVonMangoldt x n * eta1 ((n : ℝ) / x) ^ 2) =
        (2 / 3 : ℝ) * (1 + ε) * x := by
  apply quadratic_mass_normalize (x : ℝ) _ (by linarith)
  have h := abs_sub_le
    (∑ n ∈ Finset.range (x + 1), siftedVonMangoldt x n * eta1 ((n : ℝ) / x) ^ 2)
    (∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) * eta1 ((n : ℝ) / x) ^ 2)
    ((2 / 3 : ℝ) * x)
  have hs := quadratic_sieve_loss x hx
  have hb : (x : ℝ) / (20 * Real.log ((x : ℝ) / 10)) ≤ (x : ℝ) / 150 := by
    apply (div_le_iff₀ (by linarith : 0 < 20 * Real.log ((x : ℝ) / 10))).2
    nlinarith [mul_nonneg (show 0 ≤ (x : ℝ) by positivity)
      (show 0 ≤ Real.log ((x : ℝ) / 10) - 15 / 2 by linarith)]
  linarith

end TaoFivePrimes
