import examples.«five-primes».Theorem51GeometricKernel
import examples.«five-primes».Theorem51CosecantForm

namespace TaoFivePrimes
open Finset

lemma sin_ne_zero_short_arc (t : ℝ) (ht : t ≠ 0) (hb : |t| ≤ 8 / 5) :
    Real.sin t ≠ 0 := by
  rcases lt_or_gt_of_ne ht with h | h
  · have hs := Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr h)
      (show -t < Real.pi by linarith [neg_le_abs t, Real.pi_gt_three])
    rw [Real.sin_neg] at hs
    linarith
  · exact (Real.sin_pos_of_pos_of_lt_pi h
      (by linarith [le_abs_self t, Real.pi_gt_three])).ne'

/-- Off-diagonal geometric kernel represented by two unit phases. -/
lemma angular_kernel_two_phases (k u v : ℝ) (N : ℕ)
    (ht : Real.sin (k * (u - v)) ≠ 0) :
    (∑ j ∈ range N, star (angularPhase ((-2 * (j : ℝ) * k) * u)) *
      angularPhase ((-2 * (j : ℝ) * k) * v)) =
    ((star (angularPhase ((-(2 * (N : ℝ) - 1) * k) * u)) *
        angularPhase ((-(2 * (N : ℝ) - 1) * k) * v) -
      star (angularPhase (k * u)) * angularPhase (k * v)) / (2 * Complex.I)) *
      ((1 / Real.sin (k * (u - v)) : ℝ) : ℂ) := by
  simp only [angularPhase_star_mul]
  have harg (j : ℕ) : -2 * (j : ℝ) * k * (v - u) =
      2 * (j : ℝ) * (k * (u - v)) := by ring
  simp only [harg]
  rw [angular_geometric_cosecant _ N ht]
  congr 3 <;> congr 1 <;> ring

/-- Finite large-sieve estimate on a half-modulus integer block.
The conclusion concerns the actual exponential sums, not an assumed kernel bound. -/
theorem unit_finite_large_sieve {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (q h : ℝ) (hq : 100 ≤ q)
    (hlo : (q - 1) / q ^ 2 ≤ h) (hhi : h ≤ (q + 1) / q ^ 2)
    (hwidth : ∀ m n, |(idx m : ℝ) - (idx n : ℝ)| ≤ q / 2)
    (hcard : (Fintype.card ι : ℝ) - 1 ≤ q / 2) (N : ℕ) (x : ι → ℂ) :
    (∑ j ∈ range N, ‖∑ m, angularPhase ((-2 * (j : ℝ) * (Real.pi * h)) * idx m) * x m‖ ^ 2) ≤
      ((N : ℝ) + 2 * q - 1) * ∑ m, ‖x m‖ ^ 2 := by
  let k := Real.pi * h
  let A (j : ℕ) (m : ι) := angularPhase ((-2 * (j : ℝ) * k) * idx m)
  let K (m n : ι) := ∑ j ∈ range N, star (A j m) * A j n
  let O : ℂ := ∑ m, ∑ n ∈ univ.erase m, star (x m) * K m n * x n
  have hh : 0 < h := lt_of_lt_of_le (div_pos (by linarith) (by positivity)) hlo
  have hkn (m n : ι) (hmn : n ≠ m) : Real.sin (k * ((idx m : ℝ) - (idx n : ℝ))) ≠ 0 := by
    apply sin_ne_zero_short_arc
    · apply mul_ne_zero (mul_pos Real.pi_pos hh).ne'
      intro he
      apply hmn
      apply hinj
      exact_mod_cast (sub_eq_zero.mp he).symm
    · exact unit_kernel_angle q h _ hq hh.le hhi (hwidth m n)
  have hO : ‖O‖ ≤ (2 * q - 1) * ∑ m, ‖x m‖ ^ 2 := by
    have hb := unit_cosecant_phase_difference idx hinj q h hq hlo hhi hwidth hcard
      (fun m => angularPhase ((-(2 * (N : ℝ) - 1) * k) * idx m))
      (fun m => angularPhase (k * idx m)) x
      (fun m => angularPhase_norm _) (fun m => angularPhase_norm _)
    convert hb using 1
    congr 1
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro n hn
    dsimp [K, A]
    have he := angular_kernel_two_phases k (idx m) (idx n) N (hkn m n (mem_erase.mp hn).1)
    simp only [Complex.star_def] at he
    rw [he]
    ring
  have hdiag (m : ι) : K m m = (N : ℂ) := by
    simp only [K, A, angularPhase_star_mul, sub_self, mul_zero, angularPhase_zero,
      sum_const, card_range, nsmul_eq_mul, mul_one]
  have hgram := finite_gram_expansion (range N) A x
  have hsplit : (∑ m, ∑ n, star (x m) * K m n * x n) =
      (((N : ℝ) * ∑ m, ‖x m‖ ^ 2 : ℝ) : ℂ) + O := by
    have hs (m : ι) : (∑ n, star (x m) * K m n * x n) =
        (N : ℂ) * (star (x m) * x m) +
        ∑ n ∈ univ.erase m, star (x m) * K m n * x n := by
      rw [← sum_erase_add _ _ (mem_univ m), hdiag]
      ring
    simp only [Complex.star_def] at hs ⊢
    simp only [hs, sum_add_distrib, ← mul_sum, Complex.conj_mul']
    simp only [O, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_pow,
      Complex.ofReal_natCast, Complex.star_def]
  change _ = ∑ m, ∑ n, star (x m) * K m n * x n at hgram
  rw [hsplit] at hgram
  have hn := congrArg norm hgram
  have hnonneg : 0 ≤ ∑ j ∈ range N, ‖∑ m, A j m * x m‖ ^ 2 := sum_nonneg fun j hj => sq_nonneg _
  have henergy : 0 ≤ (N : ℝ) * ∑ m, ‖x m‖ ^ 2 := mul_nonneg (Nat.cast_nonneg _) (sum_nonneg fun m hm => sq_nonneg _)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg] at hn
  have hb := (norm_add_le (((N : ℝ) * ∑ m, ‖x m‖ ^ 2 : ℝ) : ℂ) O).trans
    (add_le_add le_rfl hO)
  rw [← hn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg henergy] at hb
  dsimp [A, k] at hb
  nlinarith

/-- Translating the row interval only rotates each coefficient by a unit phase. -/
theorem unit_finite_large_sieve_translate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (q h : ℝ) (hq : 100 ≤ q)
    (hlo : (q - 1) / q ^ 2 ≤ h) (hhi : h ≤ (q + 1) / q ^ 2)
    (hwidth : ∀ m n, |(idx m : ℝ) - (idx n : ℝ)| ≤ q / 2)
    (hcard : (Fintype.card ι : ℝ) - 1 ≤ q / 2) (N : ℕ) (t : ℝ) (x : ι → ℂ) :
    (∑ j ∈ range N, ‖∑ m, angularPhase ((-2 * ((j : ℝ) + t) * (Real.pi * h)) * idx m) * x m‖ ^ 2) ≤
      ((N : ℝ) + 2 * q - 1) * ∑ m, ‖x m‖ ^ 2 := by
  have hb := unit_finite_large_sieve idx hinj q h hq hlo hhi hwidth hcard N
    (fun m => angularPhase ((-2 * t * (Real.pi * h)) * idx m) * x m)
  simp only [norm_mul, angularPhase_norm, one_mul] at hb
  convert hb using 1
  apply sum_congr rfl
  intro j hj
  congr 2
  apply sum_congr rfl
  intro m hm
  have he : angularPhase ((-2 * ((j : ℝ) + t) * (Real.pi * h)) * idx m) =
      angularPhase ((-2 * (j : ℝ) * (Real.pi * h)) * idx m) *
        angularPhase ((-2 * t * (Real.pi * h)) * idx m) := by
    rw [← angularPhase_add]
    congr 1
    ring
  rw [he]
  ring

end TaoFivePrimes
