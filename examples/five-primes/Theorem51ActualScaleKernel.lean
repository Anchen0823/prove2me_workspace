import examples.«five-primes».Theorem51FiniteScaleBridge
import examples.«five-primes».Theorem51ScaleReindex

namespace TaoFivePrimes
open Finset MeasureTheory

lemma theorem51FiniteScaleKernel_eq_nat (x alpha U V W : ℝ) :
    theorem51FiniteScaleKernel x alpha U V W =
      theorem51NatScaleSum x alpha U V W * ((W⁻¹ : ℝ) : ℂ) := by
  unfold theorem51FiniteScaleKernel theorem51NatScaleSum
  rw [sum_comm, sum_mul]
  apply sum_congr rfl
  intro w hw
  by_cases hr : W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W ∧ w.Coprime 2
  · rw [if_pos hr, mul_sum, sum_mul]
    apply sum_congr rfl
    intro d hd
    unfold theorem51TypeIICoefficient
    split_ifs <;> simp_all only [Complex.ofReal_zero, mul_zero, zero_mul] <;> first | tauto | ring
  · rw [if_neg hr, zero_mul]
    apply sum_eq_zero
    intro d hd
    unfold theorem51TypeIICoefficient
    split_ifs <;> simp_all only [Complex.ofReal_zero, mul_zero, zero_mul] <;> tauto

/-- Exact connection from the integrable finite kernel to the proved scale sum. -/
lemma theorem51FiniteScaleKernel_eq_scale (x alpha U V W : ℝ)
    (hx : 0 < x) (hW : 1 ≤ W) (hWx : W ≤ x) :
    theorem51FiniteScaleKernel x alpha U V W =
      theorem51ScaleSum x alpha U V W * ((W⁻¹ : ℝ) : ℂ) := by
  rw [theorem51FiniteScaleKernel_eq_nat, theorem51NatScaleSum_eq x alpha U V W hx hW hWx]

lemma theorem51FiniteScaleKernel_norm (x alpha U V W : ℝ)
    (hx : 0 < x) (hW : 1 ≤ W) (hWx : W ≤ x) :
    ‖theorem51FiniteScaleKernel x alpha U V W‖ =
      ‖theorem51ScaleSum x alpha U V W‖ / W := by
  rw [theorem51FiniteScaleKernel_eq_scale x alpha U V W hx hW hWx, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ W⁻¹)]
  rfl

end TaoFivePrimes

