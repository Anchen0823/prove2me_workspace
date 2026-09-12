import Definitions.Def_TaoFivePrimes_Theorem51Sums
import examples.«five-primes».Theorem51CutoffAmplitude

namespace TaoFivePrimes
open Finset

noncomputable def theorem51TypeIISummand (x alpha U V : ℝ) (d w : ℕ) : ℂ :=
  if U < (d : ℝ) ∧ V < (w : ℝ) ∧ d.Coprime 2 ∧ w.Coprime 2 then
    (ArithmeticFunction.moebius d : ℂ) * (theorem51Centered V w : ℂ) *
      expCircle (alpha * d * w) * (eta0 ((d : ℝ) * w / x) : ℂ)
  else 0

lemma theorem51TypeIISummand_zero_outside (x alpha U V : ℝ) (d w : ℕ)
    (hx : 0 < x) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hout : d ∉ Icc 1 ⌈x⌉₊ ∨ w ∉ Icc 1 ⌈x⌉₊) :
    theorem51TypeIISummand x alpha U V d w = 0 := by
  unfold theorem51TypeIISummand
  split_ifs with h
  · have hd1 : (1 : ℝ) ≤ d := by linarith [h.1]
    have hw1 : (1 : ℝ) ≤ w := by linarith [h.2.1]
    have hdn : 1 ≤ d := by exact_mod_cast hd1
    have hwn : 1 ≤ w := by exact_mod_cast hw1
    have hlarge : x < (d : ℝ) ∨ x < (w : ℝ) := by
      rcases hout with hd | hw
      · have hh : ⌈x⌉₊ < d := by simp only [mem_Icc] at hd; omega
        have hc : (⌈x⌉₊ : ℝ) < d := by exact_mod_cast hh
        exact Or.inl ((Nat.le_ceil x).trans_lt hc)
      · have hh : ⌈x⌉₊ < w := by simp only [mem_Icc] at hw; omega
        have hc : (⌈x⌉₊ : ℝ) < w := by exact_mod_cast hh
        exact Or.inr ((Nat.le_ceil x).trans_lt hc)
    have he : eta0 ((d : ℝ) * w / x) = 0 := by
      apply eta0_zero_above_one
      apply (le_div_iff₀ hx).mpr
      rcases hlarge with hd | hw
      · nlinarith [mul_nonneg (show (0 : ℝ) ≤ d by positivity) (sub_nonneg.mpr hw1)]
      · nlinarith [mul_nonneg (sub_nonneg.mpr hd1) (show (0 : ℝ) ≤ w by positivity)]
    rw [he, Complex.ofReal_zero, mul_zero]
  · rfl

/-- The public double tsum is exactly a finite rectangle in the positive regime. -/
lemma theorem51TypeII_finite (x alpha U V : ℝ)
    (hx : 0 < x) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    theorem51TypeII x alpha U V =
      ‖∑ d ∈ Icc 1 ⌈x⌉₊, ∑ w ∈ Icc 1 ⌈x⌉₊, theorem51TypeIISummand x alpha U V d w‖ := by
  change ‖∑' d : ℕ, ∑' w : ℕ, theorem51TypeIISummand x alpha U V d w‖ = _
  congr 1
  rw [tsum_eq_sum (s := Icc 1 ⌈x⌉₊) (fun d hd => by
    calc
      _ = ∑' w : ℕ, (0 : ℂ) := tsum_congr (fun w =>
        theorem51TypeIISummand_zero_outside x alpha U V d w hx hU hV (Or.inl hd))
      _ = 0 := tsum_zero)]
  apply sum_congr rfl
  intro d hd
  exact tsum_eq_sum (s := Icc 1 ⌈x⌉₊) (fun w hw =>
    theorem51TypeIISummand_zero_outside x alpha U V d w hx hU hV (Or.inr hw))

end TaoFivePrimes


