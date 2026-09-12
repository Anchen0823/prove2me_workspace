import examples.«five-primes».AbelErrorAssembly
import examples.«five-primes».PrimeMassReduction

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

/-- Reduction to a two-sided explicit Chebyshev estimate above 10^8. -/
theorem quadratic_mass_of_chebyshev_error (x : ℕ)
    (hx : (10 ^ 9 : ℝ) ≤ x) (hlog : 15 / 2 ≤ Real.log ((x : ℝ) / 10))
    (hsource : ∀ y : ℝ, 10 ^ 8 ≤ y →
      |Chebyshev.psi y - y| ≤ y / (40 * Real.log y)) :
    ∃ ε : ℝ, |ε| ≤ 0.02 ∧
      (∑ n ∈ Finset.range (x + 1),
        siftedVonMangoldt x n * eta1 ((n : ℝ) / x) ^ 2) =
        (2 / 3 : ℝ) * (1 + ε) * x := by
  apply quadratic_prime_mass_of_unsifted x hx hlog
  have hxpos : 0 < x := by exact_mod_cast (show (0 : ℝ) < x by linarith)
  have huniform : ∀ t ∈ Set.Ioc ((x : ℝ) / 10) (9 * (x : ℝ) / 10),
      |Chebyshev.psi t - t| ≤ (x : ℝ) / (40 * Real.log ((x : ℝ) / 10)) := by
    intro t ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have hlogs : Real.log ((x : ℝ) / 10) ≤ Real.log t :=
      Real.log_le_log (by positivity) ht.1.le
    calc
      _ ≤ t / (40 * Real.log t) := hsource t (by linarith [ht.1])
      _ ≤ t / (40 * Real.log ((x : ℝ) / 10)) :=
        div_le_div_of_nonneg_left ht0 (by linarith) (by linarith)
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith [ht.2]) (by linarith)
  have h := unsifted_mass_error_of_uniform x hxpos
    ((x : ℝ) / (40 * Real.log ((x : ℝ) / 10))) huniform
  convert h using 1 <;> ring

end TaoFivePrimes
