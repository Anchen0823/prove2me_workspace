import Definitions.Def_TaoFivePrimes_Theorem51Sums
open TaoFivePrimes

theorem TaoFivePrimes.theorem51_typeI_bound
    (x alpha beta U V : ℝ) (a : ℤ) (q : ℕ) (c : ℕ → ℂ)
    (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUVx : U * V ≤ x / 4) (hUVq : U * V < (q : ℝ) - 1)
    (ha : a.natAbs = 1)
    (hc : ∀ d ∈ theorem51Divisors U V, ‖c d‖ ≤ 1)
    (hphase : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    theorem51TypeI x alpha U V c ≤
      (96 / Real.pi ^ 2) * (x / (x / q) ^ 2) *
        Real.log (4 * x) * Real.log (4 * Real.exp 1 * q / Real.pi) := by sorry
