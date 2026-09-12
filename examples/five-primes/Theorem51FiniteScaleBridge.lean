import examples.«five-primes».Theorem51TypeIIFinite
import examples.«five-primes».Theorem51EtaScale

namespace TaoFivePrimes
open Finset MeasureTheory

noncomputable def theorem51TypeIICoefficient (alpha U V : ℝ) (d w : ℕ) : ℂ :=
  if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
    (ArithmeticFunction.moebius d : ℂ) * (theorem51Centered V w : ℂ) *
      expCircle (alpha * d * w)
  else 0

noncomputable def theorem51FiniteScaleKernel (x alpha U V W : ℝ) : ℂ :=
  ∑ d ∈ Icc 1 ⌈x⌉₊, ∑ w ∈ Icc 1 ⌈x⌉₊,
    theorem51TypeIICoefficient alpha U V d w *
      ((if x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧
        W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W then W⁻¹ else 0 : ℝ) : ℂ)

lemma theorem51TypeIISummand_factor (x alpha U V : ℝ) (d w : ℕ) :
    theorem51TypeIISummand x alpha U V d w =
      theorem51TypeIICoefficient alpha U V d w * (eta0 ((d : ℝ) * w / x) : ℂ) := by
  unfold theorem51TypeIISummand theorem51TypeIICoefficient
  split_ifs <;> simp

lemma theorem51FiniteScaleKernel_integrable (x alpha U V : ℝ) :
    Integrable (theorem51FiniteScaleKernel x alpha U V) := by
  unfold theorem51FiniteScaleKernel
  apply integrable_finsetSum
  intro d hd
  apply integrable_finsetSum
  intro w hw
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by have := (mem_Icc.mp hd).1; omega)
  have hw0 : (0 : ℝ) < w := by exact_mod_cast (show 0 < w by have := (mem_Icc.mp hw).1; omega)
  exact ((scale_pair_integrable x d w hd0 hw0).ofReal).const_mul
    (theorem51TypeIICoefficient alpha U V d w)

lemma theorem51_finite_scale_identity (x alpha U V : ℝ) (hx : 0 < x) :
    (∑ d ∈ Icc 1 ⌈x⌉₊, ∑ w ∈ Icc 1 ⌈x⌉₊, theorem51TypeIISummand x alpha U V d w) =
      4 * ∫ W : ℝ, theorem51FiniteScaleKernel x alpha U V W := by
  let s : Finset ℕ := Icc 1 ⌈x⌉₊
  have hp := finite_eta0_scale_integral (s ×ˢ s) x
    (fun p : ℕ × ℕ => (p.1 : ℝ)) (fun p : ℕ × ℕ => (p.2 : ℝ))
    (fun p => theorem51TypeIICoefficient alpha U V p.1 p.2) hx
    (fun p hp => by
      have hh := (mem_Icc.mp (mem_product.mp hp).1).1
      exact_mod_cast (show 0 < p.1 by omega))
    (fun p hp => by
      have hh := (mem_Icc.mp (mem_product.mp hp).2).1
      exact_mod_cast (show 0 < p.2 by omega))
  simpa only [sum_product, s, theorem51TypeIISummand_factor, theorem51FiniteScaleKernel] using hp

/-- The original public Type II sum now has an exact, integrable scale representation. -/
lemma theorem51TypeII_finite_scale_integral (x alpha U V : ℝ)
    (hx : 0 < x) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    theorem51TypeII x alpha U V =
      4 * ‖∫ W : ℝ, theorem51FiniteScaleKernel x alpha U V W‖ := by
  rw [theorem51TypeII_finite x alpha U V hx hU hV,
    theorem51_finite_scale_identity x alpha U V hx, norm_mul]
  norm_num

lemma theorem51TypeII_le_finite_scale_norm (x alpha U V : ℝ)
    (hx : 0 < x) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    theorem51TypeII x alpha U V ≤
      4 * ∫ W : ℝ, ‖theorem51FiniteScaleKernel x alpha U V W‖ := by
  rw [theorem51TypeII_finite_scale_integral x alpha U V hx hU hV]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by norm_num)

end TaoFivePrimes
