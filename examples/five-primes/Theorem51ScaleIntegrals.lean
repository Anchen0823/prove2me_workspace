import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

namespace TaoFivePrimes
open MeasureTheory

/-- The logarithmic weight is integrated against dW/W. -/
lemma integral_log_div_positive (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, Real.log t / t) =
      ((Real.log b) ^ 2 - (Real.log a) ^ 2) / 2 := by
  have hpos : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht => ha.trans_le ht.1
  have hc : ContinuousOn (fun t : ℝ => Real.log t / t) (Set.Icc a b) :=
    (continuousOn_id.log (fun t ht => (hpos t ht).ne')).div continuousOn_id
      (fun t ht => (hpos t ht).ne')
  have hi : IntervalIntegrable (fun t : ℝ => Real.log t / t) volume a b := hc.intervalIntegrable_of_Icc hab
  have hd : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => (Real.log t) ^ 2 / 2) (Real.log t / t) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    convert ((Real.hasDerivAt_log (hpos t ht).ne').pow 2).div_const 2 using 1 <;> first | rfl | ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  convert he using 1 <;> first | rfl | ring

lemma integral_log_div_factorized (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, Real.log t / t) = Real.log (b / a) * Real.log (a * b) / 2 := by
  have hb : 0 < b := ha.trans_le hab
  rw [integral_log_div_positive a b ha hab, Real.log_div hb.ne' ha.ne',
    Real.log_mul ha.ne' hb.ne']
  ring

end TaoFivePrimes


