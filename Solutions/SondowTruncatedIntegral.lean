import Solutions.SondowLogMoment
import Solutions.SondowKernelExpansion

open MeasureTheory Filter Set
open Finset (range)

namespace EulerMascheroni.Sondow

noncomputable abbrev squareMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioc 0 1)).prod (volume.restrict (Ioc 0 1))

theorem ae_open_square : ∀ᵐ p ∂squareMeasure, p.1 ∈ Ioo (0:ℝ) 1 ∧ p.2 ∈ Ioo (0:ℝ) 1 := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.prod measurableSet_Ioo)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (volume.ae_ne (1:ℝ))] with x hx hx1
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae (volume.ae_ne (1:ℝ))] with y hy hy1
  exact ⟨⟨hx.1, lt_of_le_of_ne hx.2 hx1⟩, ⟨hy.1, lt_of_le_of_ne hy.2 hy1⟩⟩

noncomputable def integralKernel (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  (p.1*(1-p.1)*p.2*(1-p.2))^n / ((1-p.1*p.2)*(-Real.log (p.1*p.2)))

theorem integralKernel_bound (n : ℕ) (hn : 0 < n) (p : ℝ × ℝ)
    (hp : p.1 ∈ Ioo 0 1 ∧ p.2 ∈ Ioo 0 1) :
    0 ≤ integralKernel n p ∧ integralKernel n p ≤ 1/(-Real.log (p.1*p.2)) := by
  obtain ⟨hx, hy⟩ := hp
  have ht : 0 < p.1*p.2 := mul_pos hx.1 hy.1
  have ht1 : p.1*p.2 < 1 := by nlinarith [hx.2, mul_pos hx.1 (sub_pos.mpr hy.2)]
  have hl : 0 < -Real.log (p.1*p.2) := neg_pos.mpr (Real.log_neg ht ht1)
  have hu : 0 ≤ p.1*(1-p.1)*p.2*(1-p.2) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hx.1.le (by linarith [hx.2])) hy.1.le)
      (by linarith [hy.2])
  have hu1 : p.1*(1-p.1)*p.2*(1-p.2) ≤ 1-p.1*p.2 := by
    have hprod : (1-p.1)*(1-p.2) ≤ 1-p.1*p.2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hx.2.le) hy.1.le,
        mul_nonneg (sub_nonneg.mpr hy.2.le) hx.1.le]
    have hh := mul_le_mul_of_nonneg_right ht1.le
      (mul_nonneg (sub_nonneg.mpr hx.2.le) (sub_nonneg.mpr hy.2.le))
    nlinarith
  have hpow : (p.1*(1-p.1)*p.2*(1-p.2))^n ≤ 1-p.1*p.2 := by
    exact (pow_le_of_le_one hu (by linarith) hn.ne').trans hu1
  unfold integralKernel
  refine ⟨div_nonneg (pow_nonneg hu _) (by positivity), ?_⟩
  apply (div_le_iff₀ (mul_pos (sub_pos.mpr ht1) hl)).mpr
  calc
    _ ≤ 1-p.1*p.2 := hpow
    _ = _ := by field_simp [neg_ne_zero.mp hl.ne']

theorem integralKernel_integrable (n : ℕ) (hn : 0 < n) :
    Integrable (integralKernel n) squareMeasure := by
  have hbase : Integrable (fun p : ℝ × ℝ => 1/(-Real.log (p.1*p.2))) squareMeasure := by
    simpa using logarithmic_moment_integrable 0 0 (by norm_num) (by norm_num)
  apply hbase.mono' (show Measurable (integralKernel n) from by
    unfold integralKernel; fun_prop).aestronglyMeasurable
  filter_upwards [ae_open_square] with p hp
  obtain ⟨hpos, hbound⟩ := integralKernel_bound n hn p hp
  simpa [Real.norm_of_nonneg hpos] using hbound

theorem cutoffKernel_integrable (n N : ℕ) (hn : 0 < n) :
    Integrable (fun p => integralKernel n p * (p.1*p.2)^N) squareMeasure := by
  apply (integralKernel_integrable n hn).mono'
    (show Measurable (fun p => integralKernel n p * (p.1*p.2)^N) from by
      unfold integralKernel; fun_prop).aestronglyMeasurable
  filter_upwards [ae_open_square] with p hp
  have hpos := (integralKernel_bound n hn p hp).1
  have ht : 0 ≤ p.1*p.2 := mul_nonneg hp.1.1.le hp.2.1.le
  have ht1 : p.1*p.2 ≤ 1 := by
    nlinarith [hp.1.2, mul_pos hp.1.1 (sub_pos.mpr hp.2.2)]
  rw [Real.norm_of_nonneg (mul_nonneg hpos (pow_nonneg ht _))]
  exact mul_le_of_le_one_right hpos (pow_le_one₀ ht ht1)

theorem I_eq_square_integral (n : ℕ) (hn : 0 < n) :
    I n = ∫ p, integralKernel n p ∂squareMeasure := by
  rw [integral_prod _ (integralKernel_integrable n hn)]
  simp only [I, integralKernel, intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]

theorem remainder_eq_square_integral (n N : ℕ) (hn : 0 < n) :
    remainder n N = ∫ p, integralKernel n p * (p.1*p.2)^N ∂squareMeasure := by
  rw [integral_prod _ (cutoffKernel_integrable n N hn)]
  simp only [remainder, integralKernel,
    intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]

theorem nat_moment_integrable (a b : ℕ) :
    Integrable (fun p : ℝ × ℝ => p.1^a*p.2^b/(-Real.log (p.1*p.2))) squareMeasure := by
  simpa using logarithmic_moment_integrable (a:ℝ) (b:ℝ) (by positivity) (by positivity)

theorem truncated_integral_moment_expansion (n N : ℕ) (hn : 0 < n) :
    I n - remainder n N =
      ∑ i ∈ range (n+1), ∑ j ∈ range (n+1), ∑ v ∈ range N,
        ((-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ)) *
          (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
            x^(n+i+v)*y^(n+j+v)/(-Real.log (x*y))) := by
  let F (i j v : ℕ) (p : ℝ × ℝ) : ℝ :=
    ((-1:ℝ)^(i+j)*(n.choose i:ℝ)*(n.choose j:ℝ)) *
      (p.1^(n+i+v)*p.2^(n+j+v)/(-Real.log (p.1*p.2)))
  have hF (i j v : ℕ) : Integrable (F i j v) squareMeasure :=
    (nat_moment_integrable (n+i+v) (n+j+v)).const_mul _
  rw [I_eq_square_integral n hn, remainder_eq_square_integral n N hn,
    ← integral_sub (integralKernel_integrable n hn) (cutoffKernel_integrable n N hn)]
  have he : (fun p => integralKernel n p - integralKernel n p * (p.1*p.2)^N)
      =ᵐ[squareMeasure] (fun p => ∑ i ∈ range (n+1), ∑ j ∈ range (n+1),
        ∑ v ∈ range N, F i j v p) := by
    filter_upwards [ae_open_square] with p hp
    have ht1 : p.1*p.2 < 1 := by
      nlinarith [hp.1.2, mul_pos hp.1.1 (sub_pos.mpr hp.2.2)]
    simpa only [F, integralKernel, mul_sub, mul_one] using
      truncated_kernel_expansion n N p.1 p.2 ht1.ne
  rw [integral_congr_ae he, integral_finsetSum _ (fun i hi =>
    integrable_finsetSum _ (fun j hj => integrable_finsetSum _ (fun v hv => hF i j v)))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j hj => integrable_finsetSum _ (fun v hv => hF i j v))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_finsetSum _ (fun v hv => hF i j v)]
  apply Finset.sum_congr rfl
  intro v hv
  dsimp only [F]
  rw [integral_const_mul, integral_prod _ (nat_moment_integrable (n+i+v) (n+j+v))]
  simp only [intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]

end EulerMascheroni.Sondow

#print axioms EulerMascheroni.Sondow.integralKernel_integrable
#print axioms EulerMascheroni.Sondow.truncated_integral_moment_expansion
