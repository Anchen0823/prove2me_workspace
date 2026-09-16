import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Finset.Lattice.Union
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

namespace GoldbachSieve

/-- Numbers in an interval surviving sieving by primes up to `cutoff`.
A sieving prime itself is retained. -/
def survivors (lo hi cutoff : ℕ) : Finset ℕ :=
  let primes := (Finset.Icc 2 cutoff).filter Nat.Prime
  (Finset.Icc (max 2 lo) hi).filter fun q =>
    (primes.filter (fun r => r ∣ q ∧ r ≠ q)).card = 0

/-- Sums of a small prime and a survivor in a specified interval. -/
def pairSums (smallBound lo hi cutoff : ℕ) : Finset ℕ :=
  ((Finset.Icc 2 smallBound).filter Nat.Prime).biUnion fun p =>
    (survivors lo hi cutoff).image (p + ·)

end GoldbachSieve
