import Definitions.Def_TaoFivePrimes_ArcSplit
open scoped BigOperators
open TaoFivePrimes

theorem TaoFivePrimes.eta1_quadratic_prime_mass (x : ℕ)
    (hc8 : (10 ^ 8 : ℝ) ≤ (1 / 10 : ℝ) * x)
    (hneat : (10 ^ 4 : ℝ) * (3 / 2 : ℝ) ≤ x)
    (halamo : 5 * (3 / 2 : ℝ) ≤ Real.log ((1 / 10 : ℝ) * x))
    (h10q : (10 ^ 8 : ℝ) * (9 / 4 : ℝ) ≤ x) :
    ∃ ε : ℝ, |ε| ≤ 0.02 ∧
      (∑ n ∈ Finset.range (x + 1), siftedVonMangoldt x n * eta1 ((n : ℝ) / x) ^ 2) =
        (2 / 3 : ℝ) * (1 + ε) * x := by sorry
