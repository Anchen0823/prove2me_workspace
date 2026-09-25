import Mathlib

-- Unpublished local source placeholder; not a proved theorem.
-- R. Mawia (R. Vanlalngaia, Ramdinmawia), Explicit Mertens sums, 2017
-- (zbMATH Zbl 1412.11125); as tabulated in the TME-EMT wiki (Explicit bounds on
-- primes, Art01, section 2): for x >= 2,
--     sum_{p<=x} 1/p = log log x + B + O*(4/log^3 x),
-- with B the Meissel-Mertens constant and O* an absolute-value bound; for
-- x >= 1000 the constant 4 may be replaced by 2.3, for x >= 24284 by 1.
namespace TaoFivePrimes

theorem mawia_reciprocal_sum_bound (x : ℝ) (hx : 2 ≤ x) :
    |(∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) - Real.log (Real.log x) -
        (Real.eulerMascheroniConstant +
          ∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)))| ≤
      4 / (Real.log x) ^ 3 := by sorry

end TaoFivePrimes
