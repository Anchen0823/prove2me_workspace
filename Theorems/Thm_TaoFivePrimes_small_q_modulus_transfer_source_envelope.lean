import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_RepresentationCount
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace TaoFivePrimes

theorem small_q_modulus_transfer_source_envelope
    (x alpha : ℝ) (q0 : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq0pos : 0 < q0)
    (hq0 : ∀ p ∈ q0.primeFactors, (p : ℝ) ≤ Real.sqrt x) :
    ‖smoothedExpSum eta0 q0 x alpha - smoothedExpSum eta0 2 x alpha‖ ≤
      20.16 * Real.sqrt x := by
  sorry

end TaoFivePrimes
