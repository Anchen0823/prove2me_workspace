import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

open MeasureTheory Filter Set
open scoped Topology

namespace EulerMascheroni.Sondow

theorem rational_integral (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    (∫ t in Ioi (0:ℝ), 1/((t+a)*(t+b))) = Real.log (b/a)/(b-a) := by
  let F : ℝ → ℝ := fun t => Real.log ((t+a)/(t+b))/(b-a)
  have hd (t : ℝ) (ht : t ∈ Ici (0:ℝ)) :
      HasDerivAt F (1/((t+a)*(t+b))) t := by
    have hta : t+a ≠ 0 := by linarith [ht.out]
    have htb : t+b ≠ 0 := by linarith [ht.out]
    have hba : b-a ≠ 0 := sub_ne_zero.mpr hab.symm
    have h := ((((hasDerivAt_id t).add_const a).div
      ((hasDerivAt_id t).add_const b) htb).log (div_ne_zero hta htb)).div_const (b-a)
    convert h using 1 <;> first | rfl | (dsimp; field_simp; ring)
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hi : Tendsto (fun t : ℝ => (t+b)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ b tendsto_id)
    have hratio : (fun t : ℝ => 1+(a-b)*(t+b)⁻¹) =ᶠ[atTop]
        (fun t => (t+a)/(t+b)) := by
      filter_upwards [eventually_gt_atTop (-b)] with t ht
      field_simp [show t+b ≠ 0 by linarith]; ring
    have hh' := ((tendsto_const_nhds.add (hi.const_mul (a-b))).congr' hratio).log
      (by norm_num : (1:ℝ)+(a-b)*0 ≠ 0)
    simpa [F] using hh'.div_const (b-a)
  have he := integral_Ioi_of_hasDerivAt_of_nonneg' hd
    (fun t ht => by
      have ht0 : 0 < t := ht
      positivity : ∀ t ∈ Ioi (0:ℝ), 0 ≤ 1/((t+a)*(t+b))) hlim
  change (∫ t in Ioi (0:ℝ), 1/((t+a)*(t+b))) = _ at he
  rw [he]
  simp only [F, zero_add]
  rw [Real.log_div hb.ne' ha.ne', Real.log_div ha.ne' hb.ne']
  ring

theorem rational_integral_diagonal (a : ℝ) (ha : 0 < a) :
    (∫ t in Ioi (0:ℝ), 1/((t+a)*(t+a))) = 1/a := by
  let F : ℝ → ℝ := fun t => -(t+a)⁻¹
  have hd (t : ℝ) (ht : t ∈ Ici (0:ℝ)) :
      HasDerivAt F (1/((t+a)*(t+a))) t := by
    have hta : t+a ≠ 0 := by linarith [ht.out]
    have h := (((hasDerivAt_id t).add_const a).inv hta).neg
    convert h using 1 <;> first | rfl | (dsimp; field_simp)
  have hlim : Tendsto F atTop (𝓝 0) := by
    simpa [F] using (tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ a tendsto_id)).neg
  have he := integral_Ioi_of_hasDerivAt_of_nonneg' hd
    (fun t ht => by
      have ht0 : 0 < t := ht
      positivity : ∀ t ∈ Ioi (0:ℝ), 0 ≤ 1/((t+a)*(t+a))) hlim
  simpa [F, one_div] using he

/-- Laplace representation of the reciprocal logarithm on the open unit interval. -/
theorem reciprocal_log_integral (z : ℝ) (hz : 0 < z) (hz1 : z < 1) :
    (∫ t in Ioi (0:ℝ), z ^ t) = 1 / (-Real.log z) := by
  have hl : Real.log z < 0 := Real.log_neg hz hz1
  have he := integral_exp_mul_Ioi hl 0
  simpa [Real.rpow_def_of_pos hz, div_eq_mul_inv] using he

theorem reciprocal_log_integrable (z : ℝ) (hz : 0 < z) (hz1 : z < 1) :
    IntegrableOn (fun t : ℝ => z ^ t) (Ioi (0:ℝ)) := by
  simpa [Real.rpow_def_of_pos hz] using
    integrableOn_exp_mul_Ioi (Real.log_neg hz hz1) 0

/-- Integrability is recovered from the nonzero evaluated integral, using Lean's
totalized Bochner integral convention. No integrability hypothesis is hidden. -/
theorem rational_integrable (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => 1/((t+a)*(t+b))) (Ioi (0:ℝ)) := by
  by_contra hi
  have hz := integral_undef hi
  by_cases hab : a = b
  · subst b
    rw [rational_integral_diagonal a ha] at hz
    exact (div_ne_zero one_ne_zero ha.ne') hz
  · rw [rational_integral a b ha hb hab] at hz
    have hr : b/a ≠ 1 := by
      intro he
      have : b = a := (div_eq_one_iff_eq ha.ne').mp he
      exact hab this.symm
    exact (div_ne_zero (Real.log_ne_zero_of_pos_of_ne_one (div_pos hb ha) hr)
      (sub_ne_zero.mpr (Ne.symm hab))) hz

/-- The one-dimensional moments used after introducing the Laplace parameter. -/
theorem unit_rpow_integral (r : ℝ) (hr : -1 < r) :
    (∫ x in (0:ℝ)..1, x ^ r) = 1/(r+1) := by
  simpa [Real.zero_rpow (show r+1 ≠ 0 by linarith)] using
    integral_rpow (a := (0:ℝ)) (b := 1) (Or.inl hr)

end EulerMascheroni.Sondow

#print axioms EulerMascheroni.Sondow.rational_integral
#print axioms EulerMascheroni.Sondow.rational_integral_diagonal
#print axioms EulerMascheroni.Sondow.reciprocal_log_integral
#print axioms EulerMascheroni.Sondow.reciprocal_log_integrable
#print axioms EulerMascheroni.Sondow.rational_integrable
#print axioms EulerMascheroni.Sondow.unit_rpow_integral
