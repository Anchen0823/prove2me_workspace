import Theorems.Thm_TaoFivePrimes_mertens_tail_le_partial_sum
import Theorems.Thm_TaoFivePrimes_reciprocal_prime_sum_upper_bound
import Theorems.Thm_TaoFivePrimes_reciprocal_prime_sum_upper_bound_strict
import Mathlib

/-!
# Reduction of `TaoFivePrimes.rosser_schoenfeld_product_log_bound_large`

Target (Rosser--Schoenfeld 1962, (3.29) in logarithmic form):

    for every real x >= 10^8,
      sum_{p <= floor x} log (p/(p-1)) < gamma + log log x + log (1 + 1/(2 log^2 x)).

The reduction splits the summand with the identity, valid for every prime `p`,

    log (p/(p-1)) = 1/p - (log (1 - 1/p) + 1/p),

which is the termwise form of `log prod p/(p-1) = sum 1/p - sum (log(1-1/p) + 1/p)`.
Summing over `Nat.primesLE ⌊x⌋₊` reduces the target to

  * an upper bound for `sum_{p <= x} 1/p` — the analytic input, published as
    `TaoFivePrimes.reciprocal_prime_sum_upper_bound`
    (non-strict) and `TaoFivePrimes.reciprocal_prime_sum_upper_bound_strict`
    (strict; the target needs strictness), both stated with Mertens' constant
    expressed as `gamma + sum'_p (log (1 - 1/p) + 1/p)`, so that it cancels; and
  * `TaoFivePrimes.mertens_tail_le_partial_sum`, which says that the full series
    over primes is dominated by every finite partial sum — the elementary half,
    requiring only convergence and the sign of the terms.

The constant cancels exactly: writing `T` for the series, the strict input gives
`sum 1/p < log log x + gamma + T + delta(x)`, the tail input gives `T <= sum (log(1-1/p) + 1/p)`,
and subtracting yields `sum log (p/(p-1)) < gamma + log log x + delta(x)`.

Nothing else is assumed: the file has no `sorry`, no `axiom`, and imports only
the three platform nodes named above plus Mathlib.
-/

theorem solution (x : ℝ) (hx : 10 ^ 8 ≤ x) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log ((p : ℝ) / ((p : ℝ) - 1)) <
      Real.eulerMascheroniConstant + Real.log (Real.log x) +
        Real.log (1 + 1 / (2 * (Real.log x) ^ 2)) := by
  have hA := TaoFivePrimes.reciprocal_prime_sum_upper_bound x hx
  have hAs := TaoFivePrimes.reciprocal_prime_sum_upper_bound_strict x hx
  have hB := TaoFivePrimes.mertens_tail_le_partial_sum x
  have hid : ∀ p ∈ Nat.primesLE ⌊x⌋₊,
      Real.log ((p : ℝ) / ((p : ℝ) - 1)) =
        1 / (p : ℝ) - (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) := by
    intro p hp
    have hp' : p.Prime := by
      rw [Nat.primesLE_eq_filter_range] at hp
      exact (Finset.mem_filter.mp hp).2
    have hp2 : 2 ≤ p := hp'.two_le
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hsub : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hlog₁ : Real.log ((p : ℝ) / ((p : ℝ) - 1)) =
        Real.log (p : ℝ) - Real.log ((p : ℝ) - 1) :=
      Real.log_div (ne_of_gt hp0) (ne_of_gt hsub)
    have hlog₂ : Real.log (1 - 1 / (p : ℝ)) =
        Real.log ((p : ℝ) - 1) - Real.log (p : ℝ) := by
      have heq : 1 - 1 / (p : ℝ) = ((p : ℝ) - 1) / (p : ℝ) := by field_simp
      rw [heq, Real.log_div (ne_of_gt hsub) (ne_of_gt hp0)]
    rw [hlog₁, hlog₂]
    ring
  have hsum₁ : ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log ((p : ℝ) / ((p : ℝ) - 1))
      = (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ))
        - ∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ)) := by
    rw [Finset.sum_congr rfl hid, Finset.sum_sub_distrib]
  have hweak : (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ))
        - ∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))
      ≤ Real.eulerMascheroniConstant + Real.log (Real.log x)
        + Real.log (1 + 1 / (2 * (Real.log x) ^ 2)) := by
    linarith [hA, hB]
  have hstrict : (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ))
        - ∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))
      < Real.eulerMascheroniConstant + Real.log (Real.log x)
        + Real.log (1 + 1 / (2 * (Real.log x) ^ 2)) := by
    linarith [hAs, hB]
  rw [hsum₁]
  exact hstrict
