import examples.«five-primes».Theorem51BilinearBlock
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

namespace TaoFivePrimes
open Finset

/-- Conjugation changes the sign of the frequency without changing the bound. -/
theorem unit_bilinear_block_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (q h : ℝ) (hq : 100 ≤ q)
    (hlo : (q - 1) / q ^ 2 ≤ h) (hhi : h ≤ (q + 1) / q ^ 2)
    (hwidth : ∀ m n, |(idx m : ℝ) - (idx n : ℝ)| ≤ q / 2)
    (N : ℕ) (t : ℝ) (a : ℕ → ℂ) (x : ι → ℂ) :
    ‖∑ j ∈ range N, a j *
      (∑ m, angularPhase ((2 * ((j : ℝ) + t) * (Real.pi * h)) * idx m) * x m)‖ ≤
      Real.sqrt (((N : ℝ) + 2 * q - 1) * (∑ m, ‖x m‖ ^ 2) * ∑ j ∈ range N, ‖a j‖ ^ 2) := by
  have hb := unit_bilinear_block idx hinj q h hq hlo hhi hwidth N t
    (fun j => star (a j)) (fun m => star (x m))
  simp only [norm_star] at hb
  rw [← norm_star (∑ j ∈ range N, star (a j) *
    (∑ m, angularPhase ((-2 * ((j : ℝ) + t) * (Real.pi * h)) * idx m) * star (x m)))] at hb
  simp only [star_sum, star_mul, star_star, angularPhase_star] at hb
  have he (j : ℕ) (m : ι) : -((-2 * ((j : ℝ) + t) * (Real.pi * h)) * idx m) =
      (2 * ((j : ℝ) + t) * (Real.pi * h)) * idx m := by ring
  simp only [he] at hb
  simpa only [mul_comm] using hb

/-- Exact phase identity for odd columns and consecutive odd rows. -/
lemma odd_bilinear_phase (alpha t : ℝ) (j : ℕ) (m : ℤ) :
    expCircle (alpha * ((2 * m + 1 : ℤ) : ℝ) * (2 * ((j : ℝ) + t))) =
      angularPhase ((2 * ((j : ℝ) + t) * (Real.pi * (4 * alpha))) * m) *
        expCircle (alpha * (2 * ((j : ℝ) + t))) := by
  unfold expCircle angularPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma expCircle_norm_one (t : ℝ) : ‖expCircle t‖ = 1 := by
  simp [expCircle, Complex.norm_exp]

/-- The actual e(alpha*d*w) kernel on odd columns and consecutive odd rows. -/
theorem unit_odd_bilinear_block {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (q alpha : ℝ) (hq : 100 ≤ q)
    (hlo : (q - 1) / q ^ 2 ≤ 4 * alpha) (hhi : 4 * alpha ≤ (q + 1) / q ^ 2)
    (hwidth : ∀ m n, |(idx m : ℝ) - (idx n : ℝ)| ≤ q / 2)
    (N : ℕ) (t : ℝ) (a : ℕ → ℂ) (x : ι → ℂ) :
    ‖∑ j ∈ range N, a j *
      (∑ m, expCircle (alpha * ((2 * idx m + 1 : ℤ) : ℝ) *
        (2 * ((j : ℝ) + t))) * x m)‖ ≤
      Real.sqrt (((N : ℝ) + 2 * q - 1) * (∑ m, ‖x m‖ ^ 2) * ∑ j ∈ range N, ‖a j‖ ^ 2) := by
  have hb := unit_bilinear_block_positive idx hinj q (4 * alpha) hq hlo hhi hwidth N t
    (fun j => a j * expCircle (alpha * (2 * ((j : ℝ) + t)))) x
  simp only [norm_mul, expCircle_norm_one, mul_one] at hb
  convert hb using 1
  congr 1
  simp only [odd_bilinear_phase, mul_sum]
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro m hm
  ring

end TaoFivePrimes
