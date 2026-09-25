import Mathlib

-- Unpublished local source placeholder; not a proved theorem.
-- Rosser & Schoenfeld (1962), Lemma 13, inequality (8.9) on p. 86 (non-strict form).
namespace TaoFivePrimes

theorem reciprocal_prime_sum_upper_bound (x : ℝ) (hx : 10 ^ 8 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) ≤
      Real.log (Real.log x) + Real.eulerMascheroniConstant +
        (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) +
        Real.log (1 + 1 / (2 * (Real.log x) ^ 2)) := by sorry

end TaoFivePrimes
