import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

namespace TaoFivePrimes

theorem smoothedExpSum_zero_modulus (eta : ℝ → ℝ) (x alpha : ℝ) :
    smoothedExpSum eta 0 x alpha = 0 := by
  unfold smoothedExpSum
  calc
    _ = ∑' _ : ℕ, (0 : ℂ) := by
      apply tsum_congr
      intro n
      by_cases hn : n = 1
      · subst n
        simp
      · simp [Nat.coprime_zero_right, hn]
    _ = 0 := tsum_zero

end TaoFivePrimes
