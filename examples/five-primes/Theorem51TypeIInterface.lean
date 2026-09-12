import Definitions.Def_TaoFivePrimes_Theorem51Sums
import examples.«five-primes».Theorem51TypeIActual

namespace TaoFivePrimes

/-- The complete Type I bound expressed in the public decomposition interface. -/
theorem theorem51_typeI_bound
    (x alpha beta U V : ℝ) (a : ℤ) (q : ℕ) (c : ℕ → ℂ)
    (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUVx : U * V ≤ x / 4) (hUVq : U * V < (q : ℝ) - 1)
    (ha : a.natAbs = 1)
    (hc : ∀ d ∈ theorem51Divisors U V, ‖c d‖ ≤ 1)
    (hphase : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    theorem51TypeI x alpha U V c ≤
      (96 / Real.pi ^ 2) * (x / (x / q) ^ 2) *
        Real.log (4 * x) * Real.log (4 * Real.exp 1 * q / Real.pi) := by
  have hUV : 0 ≤ U * V := mul_nonneg (by linarith) (by linarith)
  have hm := mul_nonneg (show 0 ≤ U - 40 by linarith) (show 0 ≤ V - 40 by linarith)
  have hx : 1 ≤ x := by nlinarith
  apply unit_typeI_actual_sum x alpha beta U V a q (theorem51Divisors U V) c
    hx hU hV hUVx hUVq ha _ hc hphase hbeta
  intro d hd
  obtain ⟨hd, hodd⟩ := Finset.mem_filter.mp hd
  obtain ⟨hd1, hdUV⟩ := Finset.mem_Icc.mp hd
  refine ⟨hd1, ?_, hodd⟩
  exact (Nat.cast_le.mpr hdUV).trans (Nat.floor_le hUV)

end TaoFivePrimes
