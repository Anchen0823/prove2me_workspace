import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

namespace TaoFivePrimes
open Finset

/-- The angular additive character used in the finite Gram calculation. -/
noncomputable def angularPhase (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

lemma angularPhase_add (s t : ℝ) :
    angularPhase (s + t) = angularPhase s * angularPhase t := by
  simp only [angularPhase, Complex.ofReal_add, add_mul, Complex.exp_add]

lemma angularPhase_norm (t : ℝ) : ‖angularPhase t‖ = 1 := by
  simp [angularPhase, Complex.norm_exp]

lemma angularPhase_sine (t : ℝ) :
    2 * Complex.I * (Real.sin t : ℂ) = angularPhase t - angularPhase (-t) := by
  unfold angularPhase
  rw [Complex.exp_ofReal_mul_I t, Complex.exp_ofReal_mul_I (-t)]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

/-- Finite geometric-sum identity without a division or nonvanishing assumption. -/
theorem angular_geometric_kernel (t : ℝ) (N : ℕ) :
    (2 * Complex.I * (Real.sin t : ℂ)) *
      (∑ j ∈ range N, angularPhase (2 * (j : ℝ) * t)) =
      angularPhase ((2 * (N : ℝ) - 1) * t) - angularPhase (-t) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, mul_add, ih]
    have hplus : angularPhase ((2 * ((N + 1 : ℕ) : ℝ) - 1) * t) =
        angularPhase (2 * (N : ℝ) * t) * angularPhase t := by
      rw [← angularPhase_add]
      congr 1
      push_cast
      ring
    have hminus : angularPhase ((2 * (N : ℝ) - 1) * t) =
        angularPhase (2 * (N : ℝ) * t) * angularPhase (-t) := by
      rw [← angularPhase_add]
      congr 1
      ring
    rw [hplus, hminus, angularPhase_sine]
    ring

theorem angular_geometric_cosecant (t : ℝ) (N : ℕ) (ht : Real.sin t ≠ 0) :
    (∑ j ∈ range N, angularPhase (2 * (j : ℝ) * t)) =
      (angularPhase ((2 * (N : ℝ) - 1) * t) - angularPhase (-t)) /
        (2 * Complex.I) * ((1 / Real.sin t : ℝ) : ℂ) := by
  have hs : (Real.sin t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have hi := angular_geometric_kernel t N
  rw [Complex.ofReal_div, Complex.ofReal_one, ← hi]
  field_simp
  apply sum_congr rfl
  intro j hj
  congr 1
  ring

lemma angularPhase_star (t : ℝ) : star (angularPhase t) = angularPhase (-t) := by
  simp only [angularPhase, Complex.star_def, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  congr 1
  ring

lemma angularPhase_star_mul (c u v : ℝ) :
    star (angularPhase (c * u)) * angularPhase (c * v) =
      angularPhase (c * (v - u)) := by
  rw [angularPhase_star, ← angularPhase_add]
  congr 1
  ring

lemma angularPhase_zero : angularPhase 0 = 1 := by simp [angularPhase]

/-- Pure finite algebra for the Gram matrix of a family of coefficient rows. -/
theorem finite_gram_expansion {ι J : Type*} [Fintype ι]
    (s : Finset J) (A : J → ι → ℂ) (x : ι → ℂ) :
    ((∑ j ∈ s, ‖∑ m, A j m * x m‖ ^ 2 : ℝ) : ℂ) =
      ∑ m, ∑ n, star (x m) * (∑ j ∈ s, star (A j m) * A j n) * x n := by
  have hn (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
    rw [Complex.star_def, Complex.conj_mul']
    exact Complex.ofReal_pow _ _
  rw [Complex.ofReal_sum]
  simp only [hn, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro m hm
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro j hj
  ring

end TaoFivePrimes
