import examples.«five-primes».Theorem51ScaleIntervals

namespace TaoFivePrimes
open Finset

lemma theorem51ScaleSum_zero_below (x alpha U V W : ℝ) (hWV : W ≤ V) :
    theorem51ScaleSum x alpha U V W = 0 := by
  unfold theorem51ScaleSum
  apply sum_eq_zero
  intro w hw
  have hh := (mem_oddRealInterval (W / 2) W w).mp hw
  simp [scaleRowCoefficient, not_lt.mpr (hh.2.1.trans hWV)]

lemma theorem51ScaleSum_zero_above (x alpha U V W : ℝ)
    (hU : 0 < U) (hW : 0 < W) (hUW : x / U ≤ W) :
    theorem51ScaleSum x alpha U V W = 0 := by
  have hx : x / W ≤ U := by
    apply (div_le_iff₀ hW).mpr
    have hh := (div_le_iff₀ hU).mp hUW
    nlinarith
  unfold theorem51ScaleSum
  apply sum_eq_zero
  intro w hw
  have hz : (∑ n ∈ oddHalfInterval (x / (2 * W)) (x / W),
      expCircle (alpha * ((2 * n + 1 : ℤ) : ℝ) * w) * scaleColumnCoefficient U n) = 0 := by
    apply sum_eq_zero
    intro n hn
    have hh := (mem_oddHalfInterval (x / (2 * W)) (x / W) n).mp hn
    simp only [scaleColumnCoefficient, if_neg (not_lt.mpr (hh.2.trans hx)), mul_zero]
  rw [hz, mul_zero]

end TaoFivePrimes

