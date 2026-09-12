import examples.«five-primes».Theorem51ActualScaleKernel

namespace TaoFivePrimes
open Finset MeasureTheory

lemma finite_scale_kernel_zero_of_no_pairs (x alpha U V W : ℝ)
    (h : ∀ d w : ℕ,
      (U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2) →
      (x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧ W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W) → False) :
    theorem51FiniteScaleKernel x alpha U V W = 0 := by
  unfold theorem51FiniteScaleKernel
  apply sum_eq_zero
  intro d hd
  apply sum_eq_zero
  intro w hw
  by_cases hg : U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2
  · have hn := h d w hg
    simp only [theorem51TypeIICoefficient, if_pos hg, if_neg hn, Complex.ofReal_zero, mul_zero]
  · simp only [theorem51TypeIICoefficient, if_neg hg, zero_mul]

lemma finite_scale_kernel_zero_below (x alpha U V W : ℝ) (hWV : W ≤ V) :
    theorem51FiniteScaleKernel x alpha U V W = 0 := by
  apply finite_scale_kernel_zero_of_no_pairs
  intro d w hg hi
  linarith [hg.2.1, hi.2.2.2]

lemma finite_scale_kernel_zero_above (x alpha U V W : ℝ)
    (hU : 0 < U) (hW : 0 < W) (hWU : x / U ≤ W) :
    theorem51FiniteScaleKernel x alpha U V W = 0 := by
  have hx : x / W ≤ U := by
    apply (div_le_iff₀ hW).mpr
    have hh := (div_le_iff₀ hU).mp hWU
    nlinarith
  apply finite_scale_kernel_zero_of_no_pairs
  intro d w hg hi
  linarith [hg.1, hi.2.1]

/-- The actual public Type II sum is bounded by the actual proved scale sum,
integrated over its exact parameter interval. -/
theorem theorem51TypeII_le_scale_integral (x alpha U V : ℝ)
    (hx : 0 < x) (hU : 1 ≤ U) (hV : 1 ≤ V) (hUV : U * V ≤ x) :
    theorem51TypeII x alpha U V ≤
      4 * ∫ W in V..(x / U), ‖theorem51ScaleSum x alpha U V W‖ / W := by
  have hu : 0 < U := by linarith
  have hVU : V ≤ x / U := (le_div_iff₀ hu).mpr (by nlinarith)
  have hUx : x / U ≤ x := (div_le_iff₀ hu).mpr (by nlinarith)
  have he : (∫ W : ℝ, ‖theorem51FiniteScaleKernel x alpha U V W‖) =
      ∫ W in V..(x / U), ‖theorem51ScaleSum x alpha U V W‖ / W := by
    calc
      _ = ∫ W in Set.Icc V (x / U), ‖theorem51FiniteScaleKernel x alpha U V W‖ := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro W hW
        simp only [Set.mem_Icc, not_and_or, not_le] at hW
        rcases hW with hlo | hhi
        · rw [finite_scale_kernel_zero_below x alpha U V W hlo.le, norm_zero]
        · rw [finite_scale_kernel_zero_above x alpha U V W hu
            ((div_pos hx hu).trans hhi) hhi.le, norm_zero]
      _ = ∫ W in Set.Icc V (x / U), ‖theorem51ScaleSum x alpha U V W‖ / W := by
        apply setIntegral_congr_fun measurableSet_Icc
        intro W hW
        exact theorem51FiniteScaleKernel_norm x alpha U V W hx (hV.trans hW.1)
          (hW.2.trans hUx)
      _ = _ := by rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hVU]
  exact (theorem51TypeII_le_finite_scale_norm x alpha U V hx hU hV).trans_eq (congrArg (4 * ·) he)

lemma theorem51_scale_weight_integrable (x alpha U V : ℝ)
    (hx : 0 < x) (hU : 1 ≤ U) (hV : 1 ≤ V) (hUV : U * V ≤ x) :
    IntervalIntegrable (fun W : ℝ => ‖theorem51ScaleSum x alpha U V W‖ / W)
      volume V (x / U) := by
  have hu : 0 < U := by linarith
  have hVU : V ≤ x / U := (le_div_iff₀ hu).mpr (by nlinarith)
  have hUx : x / U ≤ x := (div_le_iff₀ hu).mpr (by nlinarith)
  have hf : IntervalIntegrable (fun W => ‖theorem51FiniteScaleKernel x alpha U V W‖)
      volume V (x / U) := (theorem51FiniteScaleKernel_integrable x alpha U V).norm.intervalIntegrable
  apply hf.congr
  intro W hW
  rw [Set.uIoc_of_le hVU] at hW
  exact theorem51FiniteScaleKernel_norm x alpha U V W hx (hV.trans hW.1.le) (hW.2.trans hUx)

end TaoFivePrimes
