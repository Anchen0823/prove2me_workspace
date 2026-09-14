import Solutions.SondowRationalIntegral
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Filter Set
open scoped Topology

namespace EulerMascheroni.Sondow

private noncomputable abbrev unitMeasure : Measure ℝ := volume.restrict (Ioc 0 1)

private theorem unit_rpow_set_integral (r : ℝ) (hr : -1 < r) :
    (∫ x, x ^ r ∂unitMeasure) = 1/(r+1) := by
  rw [← unit_rpow_integral r hr, intervalIntegral.integral_of_le (by norm_num)]

private theorem unit_rpow_integrable (r : ℝ) (hr : -1 < r) :
    Integrable (fun x : ℝ => x ^ r) unitMeasure :=
  (intervalIntegral.intervalIntegrable_rpow' hr).1

private theorem parameter_moment (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht : 0 < t) :
    (∫ p : ℝ × ℝ, p.1 ^ (a+t) * p.2 ^ (b+t) ∂unitMeasure.prod unitMeasure) =
      1/((t+(a+1))*(t+(b+1))) := by
  rw [integral_prod_mul (fun x : ℝ => x ^ (a+t)) (fun y : ℝ => y ^ (b+t)),
    unit_rpow_set_integral _ (by linarith),
    unit_rpow_set_integral _ (by linarith)]
  rw [← one_div_mul_one_div]
  congr 2 <;> ring

/-- Absolute integrability needed for exchanging the Laplace parameter and the square. -/
theorem logarithmic_moment_parameter_integrable (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Integrable (fun q : ℝ × (ℝ × ℝ) => q.2.1 ^ (a+q.1) * q.2.2 ^ (b+q.1))
      ((volume.restrict (Ioi 0)).prod (unitMeasure.prod unitMeasure)) := by
  apply (integrable_prod_iff (by fun_prop)).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (unit_rpow_integrable (a+t) (by linarith [ht.out])).mul_prod
      (unit_rpow_integrable (b+t) (by linarith [ht.out]))
  · apply (rational_integrable (a+1) (b+1) (by linarith) (by linarith)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [← parameter_moment a b t ha hb ht]
    apply integral_congr_ae
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (by fun_prop) (by fun_prop))).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact (Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hx.1.le _)
      (Real.rpow_nonneg hy.1.le _))).symm

private theorem pointwise_laplace_moment (a b x y : ℝ)
    (hx : x ∈ Ioo 0 1) (hy : y ∈ Ioo 0 1) :
    (∫ t in Ioi (0:ℝ), x ^ (a+t) * y ^ (b+t)) =
      x ^ a * y ^ b / (-Real.log (x*y)) := by
  have hxy : x*y < 1 := by nlinarith [hx.2, mul_pos hx.1 (sub_pos.mpr hy.2)]
  calc
    _ = ∫ t in Ioi (0:ℝ), (x ^ a * y ^ b) * (x*y) ^ t := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => by
        dsimp only
        rw [Real.rpow_add hx.1, Real.rpow_add hy.1, Real.mul_rpow hx.1.le hy.1.le]
        ring)
    _ = _ := by
      rw [integral_const_mul, reciprocal_log_integral (x*y) (mul_pos hx.1 hy.1) hxy]
      ring

private theorem laplace_moment_ae (a b : ℝ) :
    (fun p : ℝ × ℝ => ∫ t in Ioi (0:ℝ), p.1 ^ (a+t) * p.2 ^ (b+t))
      =ᵐ[unitMeasure.prod unitMeasure]
        (fun p => p.1 ^ a * p.2 ^ b / (-Real.log (p.1*p.2))) := by
  have hmeas : Measurable (fun p : ℝ × ℝ => ∫ t in Ioi (0:ℝ),
      p.1 ^ (a+t) * p.2 ^ (b+t)) :=
    (show StronglyMeasurable (fun q : (ℝ × ℝ) × ℝ =>
      q.1.1 ^ (a+q.2) * q.1.2 ^ (b+q.2)) from by fun_prop).integral_prod_right'.measurable
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hmeas (by fun_prop))).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (volume.ae_ne (1:ℝ))] with x hx hx1
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (volume.ae_ne (1:ℝ))] with y hy hy1
  exact pointwise_laplace_moment a b x y ⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩
    ⟨hy.1, lt_of_le_of_ne hy.2 hy1⟩

theorem logarithmic_moment_integrable (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Integrable (fun p : ℝ × ℝ => p.1 ^ a * p.2 ^ b / (-Real.log (p.1*p.2)))
      ((volume.restrict (Ioc 0 1)).prod (volume.restrict (Ioc 0 1))) :=
  (logarithmic_moment_parameter_integrable a b ha hb).integral_prod_right.congr
    (laplace_moment_ae a b)

/-- The elementary double logarithmic moment reduced to a rational improper integral. -/
theorem logarithmic_moment_eq_rational (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
      x ^ a * y ^ b / (-Real.log (x*y))) =
      ∫ t in Ioi (0:ℝ), 1/((t+(a+1))*(t+(b+1))) := by
  have hi := logarithmic_moment_parameter_integrable a b ha hb
  have hs := integral_integral_swap
    (f := fun (t : ℝ) (p : ℝ × ℝ) => p.1 ^ (a+t) * p.2 ^ (b+t)) hi
  have hp : (∫ t in Ioi (0:ℝ), ∫ p : ℝ × ℝ,
      p.1 ^ (a+t) * p.2 ^ (b+t) ∂unitMeasure.prod unitMeasure) =
      ∫ t in Ioi (0:ℝ), 1/((t+(a+1))*(t+(b+1))) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact parameter_moment a b t ha hb ht
  have he : (fun p : ℝ × ℝ => ∫ t in Ioi (0:ℝ),
      p.1 ^ (a+t) * p.2 ^ (b+t)) =ᵐ[unitMeasure.prod unitMeasure]
      (fun p => p.1 ^ a * p.2 ^ b / (-Real.log (p.1*p.2))) := laplace_moment_ae a b
  have hm : Integrable (fun p : ℝ × ℝ => p.1 ^ a * p.2 ^ b / (-Real.log (p.1*p.2)))
      (unitMeasure.prod unitMeasure) := hi.integral_prod_right.congr he
  rw [integral_congr_ae he] at hs
  rw [← hp, hs, integral_prod _ hm]
  simp only [intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]

theorem logarithmic_moment_diagonal (a : ℝ) (ha : 0 ≤ a) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
      x ^ a * y ^ a / (-Real.log (x*y))) = 1/(a+1) := by
  rw [logarithmic_moment_eq_rational a a ha ha,
    rational_integral_diagonal (a+1) (by linarith)]

theorem logarithmic_moment_off_diagonal (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ≠ b) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
      x ^ a * y ^ b / (-Real.log (x*y))) = Real.log ((b+1)/(a+1))/(b-a) := by
  rw [logarithmic_moment_eq_rational a b ha hb,
    rational_integral (a+1) (b+1) (by linarith) (by linarith) (by simpa)]
  congr 1
  ring

theorem logarithmic_nat_moment_diagonal (a : ℕ) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
      x ^ a * y ^ a / (-Real.log (x*y))) = 1/(a+1:ℝ) := by
  simpa using logarithmic_moment_diagonal (a:ℝ) (by positivity)

theorem logarithmic_nat_moment_off_diagonal (a b : ℕ) (hab : a ≠ b) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
      x ^ a * y ^ b / (-Real.log (x*y))) = Real.log ((b+1:ℝ)/(a+1:ℝ))/((b:ℝ)-a) := by
  simpa using logarithmic_moment_off_diagonal (a:ℝ) (b:ℝ) (by positivity)
    (by positivity) (by exact_mod_cast hab)

end EulerMascheroni.Sondow

#print axioms EulerMascheroni.Sondow.logarithmic_moment_parameter_integrable
#print axioms EulerMascheroni.Sondow.logarithmic_moment_integrable
#print axioms EulerMascheroni.Sondow.logarithmic_moment_eq_rational
#print axioms EulerMascheroni.Sondow.logarithmic_moment_diagonal
#print axioms EulerMascheroni.Sondow.logarithmic_moment_off_diagonal
#print axioms EulerMascheroni.Sondow.logarithmic_nat_moment_diagonal
#print axioms EulerMascheroni.Sondow.logarithmic_nat_moment_off_diagonal
