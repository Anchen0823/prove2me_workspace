import Mathlib

open MeasureTheory
open scoped ComplexConjugate

namespace TaoLocalL2

/-! The functional-analytic step in Proposition 4.8 of
Tao, arXiv:1201.6656v4. The restricted measure will be the major arc. -/

theorem norm_toLp_sq {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : C(X, ℂ)) :
    ‖ContinuousMap.toLp 2 μ ℂ f‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂μ := by
  have h := ContinuousMap.inner_toLp μ f f
  rw [inner_self_eq_norm_sq_to_K] at h
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  rw [integral_complex_ofReal] at h
  simpa [← Complex.ofReal_pow] using congrArg Complex.re h


theorem correlation_sq_le {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f g : C(X, ℂ)) :
    ‖∫ t, f t * conj (g t) ∂μ‖ ^ 2 ≤
      (∫ t, ‖f t‖ ^ 2 ∂μ) * (∫ t, ‖g t‖ ^ 2 ∂μ) := by
  rw [← ContinuousMap.inner_toLp μ g f]
  calc
    ‖inner ℂ (ContinuousMap.toLp 2 μ ℂ g) (ContinuousMap.toLp 2 μ ℂ f)‖ ^ 2
        ≤ (‖ContinuousMap.toLp 2 μ ℂ g‖ * ‖ContinuousMap.toLp 2 μ ℂ f‖) ^ 2 := by
          gcongr
          exact norm_inner_le_norm _ _
    _ = _ := by rw [mul_pow, norm_toLp_sq, norm_toLp_sq, mul_comm]

/-- A lower bound from a global correlation, a bound on its complementary
arc, and the global energy of the test function. -/
theorem local_energy_lower_bound
    (f g : C(AddCircle (1 : ℝ), ℂ)) (E : Set (AddCircle (1 : ℝ)))
    (hE : MeasurableSet E) (M δ D : ℝ) (hδ : 0 ≤ δ) (hδM : δ ≤ M)
    (hD : 0 < D)
    (hmass : (∫ t, f t * conj (g t) ∂AddCircle.haarAddCircle) = (M : ℂ))
    (htail : ‖∫ t in Eᶜ, f t * conj (g t) ∂AddCircle.haarAddCircle‖ ≤ δ)
    (henergy : (∫ t, ‖g t‖ ^ 2 ∂AddCircle.haarAddCircle) ≤ D) :
    (M - δ) ^ 2 / D ≤ ∫ t in E, ‖f t‖ ^ 2 ∂AddCircle.haarAddCircle := by
  have hint : Integrable (fun t => f t * conj (g t)) AddCircle.haarAddCircle :=
    (by fun_prop : Continuous (fun t => f t * conj (g t))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsplit := integral_add_compl hE hint
  rw [hmass] at hsplit
  have htriangle := norm_add_le
    (∫ t in E, f t * conj (g t) ∂AddCircle.haarAddCircle)
    (∫ t in Eᶜ, f t * conj (g t) ∂AddCircle.haarAddCircle)
  rw [hsplit, Complex.norm_real, Real.norm_of_nonneg (hδ.trans hδM)] at htriangle
  have hlower : M - δ ≤ ‖∫ t in E, f t * conj (g t) ∂AddCircle.haarAddCircle‖ := by
    linarith
  have hcs := correlation_sq_le (AddCircle.haarAddCircle.restrict E) f g
  have hgle : (∫ t in E, ‖g t‖ ^ 2 ∂AddCircle.haarAddCircle) ≤ D := by
    apply le_trans (setIntegral_le_integral ?_ ?_) henergy
    · exact (by fun_prop : Continuous (fun t => ‖g t‖ ^ 2)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · exact Filter.Eventually.of_forall (fun _ => sq_nonneg _)
  have hfnonneg : 0 ≤ ∫ t in E, ‖f t‖ ^ 2 ∂AddCircle.haarAddCircle :=
    integral_nonneg (fun _ => sq_nonneg _)
  apply (div_le_iff₀ hD).2
  calc
    (M - δ) ^ 2 ≤ ‖∫ t in E, f t * conj (g t) ∂AddCircle.haarAddCircle‖ ^ 2 := by
      gcongr
    _ ≤ _ := hcs.trans (mul_le_mul_of_nonneg_left hgle hfnonneg)

/-- Keep the normalization and denominator loss explicit when specializing
the local energy estimate to the trapezoidal cutoff. -/
theorem normalized_major_arc_arithmetic (x ε A : ℝ) (hx : 15000 ≤ x)
    (hA : 0 ≤ A)
    (hlocal : (0.99 * ((2 / 3 : ℝ) * (1 + ε) * x)) ^ 2 ≤
      A * ((2 / 3 : ℝ) * x + 1)) :
    0.999 * (0.99 * (1 + ε)) ^ 2 * x ≤ (3 / 2 : ℝ) * A := by
  have hxpos : 0 < x := by linarith
  have hdenom : 0.999 * ((2 / 3 : ℝ) * x + 1) ≤ (2 / 3 : ℝ) * x := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hlocal (by norm_num : (0 : ℝ) ≤ 0.999)
  have hupper := mul_le_mul_of_nonneg_left hdenom hA
  apply (mul_le_mul_iff_left₀ hxpos).mp
  nlinarith

/-- The direct nonsmooth quadrature estimate loses at most 20. This still
preserves the target's 0.999 coefficient when x >= 30000. -/
theorem normalized_major_arc_arithmetic_twenty (x ε A : ℝ) (hx : 30000 ≤ x)
    (hA : 0 ≤ A)
    (hlocal : (0.99 * ((2 / 3 : ℝ) * (1 + ε) * x)) ^ 2 ≤
      A * ((2 / 3 : ℝ) * x + 20)) :
    0.999 * (0.99 * (1 + ε)) ^ 2 * x ≤ (3 / 2 : ℝ) * A := by
  have hxpos : 0 < x := by linarith
  have hdenom : 0.999 * ((2 / 3 : ℝ) * x + 20) ≤ (2 / 3 : ℝ) * x := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hlocal (by norm_num : (0 : ℝ) ≤ 0.999)
  have hupper := mul_le_mul_of_nonneg_left hdenom hA
  apply (mul_le_mul_iff_left₀ hxpos).mp
  nlinarith

end TaoLocalL2
