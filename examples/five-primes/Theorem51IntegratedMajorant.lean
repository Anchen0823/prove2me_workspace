import examples.«five-primes».Theorem51RootIntegrals
import examples.«five-primes».Theorem51ScaleIntegrals

namespace TaoFivePrimes
open MeasureTheory

noncomputable def typeIIIntegralMajorant (A B C t : ℝ) : ℝ :=
  A * (Real.log t / t) + B * (Real.log t * (1 / Real.sqrt t)) +
    C * (Real.log t * (1 / (t * Real.sqrt t)))

lemma typeII_majorant_integrable (a b A B C : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (typeIIIntegralMajorant A B C) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  unfold typeIIIntegralMajorant
  have hp : ∀ t ∈ Set.Icc a b, t ≠ 0 := fun t ht => (ha.trans_le ht.1).ne'
  have hs : ∀ t ∈ Set.Icc a b, Real.sqrt t ≠ 0 :=
    fun t ht => (Real.sqrt_pos.mpr (ha.trans_le ht.1)).ne'
  fun_prop (disch := aesop)

lemma typeII_majorant_integral_bound (a b A B C : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    (∫ t in a..b, typeIIIntegralMajorant A B C t) ≤
      (A / 2) * Real.log (b / a) * Real.log (a * b) +
        2 * (B * Real.sqrt b + C / Real.sqrt a) * Real.log b := by
  have ha0 : 0 < a := by linarith
  have hp : ∀ t ∈ Set.Icc a b, t ≠ 0 := fun t ht => (ha0.trans_le ht.1).ne'
  have hs : ∀ t ∈ Set.Icc a b, Real.sqrt t ≠ 0 :=
    fun t ht => (Real.sqrt_pos.mpr (ha0.trans_le ht.1)).ne'
  have h1 : IntervalIntegrable (fun t => A * (Real.log t / t)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    fun_prop (disch := aesop)
  have h2 : IntervalIntegrable (fun t => B * (Real.log t * (1 / Real.sqrt t))) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    fun_prop (disch := aesop)
  have h3 : IntervalIntegrable (fun t => C * (Real.log t * (1 / (t * Real.sqrt t)))) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    fun_prop (disch := aesop)
  unfold typeIIIntegralMajorant
  rw [intervalIntegral.integral_add (h1.add h2) h3, intervalIntegral.integral_add h1 h2]
  simp only [intervalIntegral.integral_const_mul]
  rw [integral_log_div_factorized a b ha0 hab]
  have hb := mul_le_mul_of_nonneg_left (integral_log_inv_sqrt_le a b ha hab) hB
  have hc := mul_le_mul_of_nonneg_left (integral_log_inv_mul_sqrt_le a b ha hab) hC
  simp only [div_eq_mul_inv] at hb hc ⊢
  nlinarith

lemma typeII_majorant_normalization (A B C W : ℝ) (hW : 0 < W) :
    (A + B * Real.sqrt W + C / Real.sqrt W) * Real.log W / W =
      typeIIIntegralMajorant A B C W := by
  have hs : Real.sqrt W ≠ 0 := (Real.sqrt_pos.mpr hW).ne'
  have he : Real.sqrt W / W = 1 / Real.sqrt W := by
    apply (div_eq_div_iff hW.ne' hs).mpr
    nlinarith [Real.sq_sqrt hW.le]
  calc
    _ = A * (Real.log W / W) + B * (Real.log W * (Real.sqrt W / W)) +
      C * (Real.log W * (1 / (W * Real.sqrt W))) := by ring
    _ = _ := by rw [he]; rfl

end TaoFivePrimes

