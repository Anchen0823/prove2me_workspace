import Mathlib

open MeasureTheory

namespace TaoFivePrimes

/-- Transfer a uniform Chebyshev error through a nonnegative continuous kernel. -/
theorem weighted_psi_error (a b δ : ℝ) (hab : a ≤ b) (g : ℝ → ℝ)
    (hg : Continuous g) (hg0 : ∀ t ∈ Set.Ioc a b, 0 ≤ g t)
    (hψ : ∀ t ∈ Set.Ioc a b, |Chebyshev.psi t - t| ≤ δ) :
    |∫ t in Set.Ioc a b, g t * (Chebyshev.psi t - t)| ≤
      δ * ∫ t in Set.Ioc a b, g t := by
  have hi : IntervalIntegrable (fun t : ℝ => Chebyshev.psi t - t) volume a b :=
    Chebyshev.psi_mono.intervalIntegrable.sub (continuous_id.intervalIntegrable a b)
  have hp : IntegrableOn (fun t => g t * (Chebyshev.psi t - t)) (Set.Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
      (hi.continuousOn_mul hg.continuousOn)
  have hq : IntegrableOn (fun t => δ * g t) (Set.Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
      ((continuous_const.mul hg).intervalIntegrable a b)
  calc
    _ ≤ ∫ t in Set.Ioc a b, |g t * (Chebyshev.psi t - t)| := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (fun t => g t * (Chebyshev.psi t - t))
          (μ := volume.restrict (Set.Ioc a b)))
    _ ≤ ∫ t in Set.Ioc a b, δ * g t := by
      apply setIntegral_mono_on hp.abs hq measurableSet_Ioc
      intro t ht
      rw [abs_mul, abs_of_nonneg (hg0 t ht)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hψ t ht) (hg0 t ht)
    _ = _ := integral_const_mul δ g

end TaoFivePrimes
