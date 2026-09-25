import Mathlib

-- Unpublished local source placeholder; not a proved theorem.
-- Rosser & Schoenfeld (1962) (2.7) + step (iii) of (3.29): the Mertens tail is
-- dominated by every finite partial sum.
namespace TaoFivePrimes

theorem mertens_tail_le_partial_sum (x : ℝ) :
    (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) ≤
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) := by sorry

end TaoFivePrimes
