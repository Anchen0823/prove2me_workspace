import examples.«five-primes».Theorem51BlockCounting
import examples.«five-primes».Theorem51FiniteLargeSieve
import Mathlib.Analysis.Real.Sqrt

namespace TaoFivePrimes
open Finset

/-- Bilinear half-block bound with no separate cardinality hypothesis. -/
theorem unit_bilinear_block_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (q h : ℝ) (hq : 100 ≤ q)
    (hlo : (q - 1) / q ^ 2 ≤ h) (hhi : h ≤ (q + 1) / q ^ 2)
    (hwidth : ∀ m n, |(idx m : ℝ) - (idx n : ℝ)| ≤ q / 2)
    (N : ℕ) (t : ℝ) (a : ℕ → ℂ) (x : ι → ℂ) :
    ‖∑ j ∈ range N, a j *
      (∑ m, angularPhase ((-2 * ((j : ℝ) + t) * (Real.pi * h)) * idx m) * x m)‖ ^ 2 ≤
      ((N : ℝ) + 2 * q - 1) * (∑ m, ‖x m‖ ^ 2) * ∑ j ∈ range N, ‖a j‖ ^ 2 := by
  let F (j : ℕ) := ∑ m, angularPhase ((-2 * ((j : ℝ) + t) * (Real.pi * h)) * idx m) * x m
  have hcard := integer_index_card_le idx hinj (q / 2) (by linarith) hwidth
  have hLS := unit_finite_large_sieve_translate idx hinj q h hq hlo hhi hwidth hcard N t x
  have hn : ‖∑ j ∈ range N, a j * F j‖ ≤ ∑ j ∈ range N, ‖a j‖ * ‖F j‖ := by
    simpa only [norm_mul] using norm_sum_le (range N) (fun j => a j * F j)
  have hsq := (sq_le_sq₀ (norm_nonneg _) (sum_nonneg fun j hj =>
    mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
  have hCS := sum_mul_sq_le_sq_mul_sq (range N) (fun j => ‖a j‖) (fun j => ‖F j‖)
  have hmul := mul_le_mul_of_nonneg_left hLS
    (show 0 ≤ ∑ j ∈ range N, ‖a j‖ ^ 2 from sum_nonneg fun j hj => sq_nonneg _)
  change ‖∑ j ∈ range N, a j * F j‖ ^ 2 ≤ _
  exact (hsq.trans hCS).trans (by simpa only [F, mul_comm, mul_left_comm, mul_assoc] using hmul)

theorem unit_bilinear_block {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (q h : ℝ) (hq : 100 ≤ q)
    (hlo : (q - 1) / q ^ 2 ≤ h) (hhi : h ≤ (q + 1) / q ^ 2)
    (hwidth : ∀ m n, |(idx m : ℝ) - (idx n : ℝ)| ≤ q / 2)
    (N : ℕ) (t : ℝ) (a : ℕ → ℂ) (x : ι → ℂ) :
    ‖∑ j ∈ range N, a j *
      (∑ m, angularPhase ((-2 * ((j : ℝ) + t) * (Real.pi * h)) * idx m) * x m)‖ ≤
      Real.sqrt (((N : ℝ) + 2 * q - 1) * (∑ m, ‖x m‖ ^ 2) * ∑ j ∈ range N, ‖a j‖ ^ 2) :=
  Real.le_sqrt_of_sq_le (unit_bilinear_block_sq idx hinj q h hq hlo hhi hwidth N t a x)

/-- Cauchy--Schwarz across blocks, retaining the number of blocks exactly. -/
lemma complex_sum_sq_le_card_energy {B : Type*} (s : Finset B) (F : B → ℂ) :
    ‖∑ b ∈ s, F b‖ ^ 2 ≤ (s.card : ℝ) * ∑ b ∈ s, ‖F b‖ ^ 2 := by
  have ht := norm_sum_le s F
  have hs := (sq_le_sq₀ (norm_nonneg _) (sum_nonneg fun b hb => norm_nonneg _)).mpr ht
  have hc := sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun b => ‖F b‖)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hc
  exact hs.trans hc

/-- Subdivision into integer half-blocks, before specializing the partition. -/
theorem unit_bilinear_blocks {B ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset B) (idx : B → ι → ℤ) (hinj : ∀ b, Function.Injective (idx b))
    (q h : ℝ) (hq : 100 ≤ q)
    (hlo : (q - 1) / q ^ 2 ≤ h) (hhi : h ≤ (q + 1) / q ^ 2)
    (hwidth : ∀ b m n, |(idx b m : ℝ) - (idx b n : ℝ)| ≤ q / 2)
    (N : ℕ) (t : ℝ) (a : ℕ → ℂ) (x : B → ι → ℂ) :
    ‖∑ b ∈ s, ∑ j ∈ range N, a j *
      (∑ m, angularPhase ((-2 * ((j : ℝ) + t) * (Real.pi * h)) * idx b m) * x b m)‖ ≤
      Real.sqrt ((s.card : ℝ) * ((N : ℝ) + 2 * q - 1) *
        (∑ b ∈ s, ∑ m, ‖x b m‖ ^ 2) * ∑ j ∈ range N, ‖a j‖ ^ 2) := by
  apply Real.le_sqrt_of_sq_le
  apply (complex_sum_sq_le_card_energy s _).trans
  have hb := sum_le_sum (s := s) (fun b hb =>
    unit_bilinear_block_sq (idx b) (hinj b) q h hq hlo hhi (hwidth b) N t a (x b))
  have hm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg s.card : (0 : ℝ) ≤ s.card)
  simpa only [← sum_mul, ← mul_sum, mul_assoc] using hm

end TaoFivePrimes
