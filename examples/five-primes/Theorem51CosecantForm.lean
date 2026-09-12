import examples.«five-primes».Theorem51IntegerHilbertForm
import examples.«five-primes».Theorem51KernelError
import examples.«five-primes».Theorem51CosecantError
import examples.«five-primes».Theorem51KernelConstants

namespace TaoFivePrimes
open Finset

/-- Integer-grid cosecant quadratic form on a short arc. -/
theorem cosecant_quadratic_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (k : ℝ) (hk : 0 < k)
    (hwidth : ∀ m n, |k * ((idx m : ℝ) - (idx n : ℝ))| ≤ 8 / 5)
    (x : ι → ℂ) :
    ‖∑ m, ∑ n ∈ univ.erase m, star (x m) *
      ((1 / Real.sin (k * ((idx m : ℝ) - (idx n : ℝ))) : ℝ) : ℂ) * x n‖ ≤
      ((7 / 2 : ℝ) / k + ((Fintype.card ι : ℝ) - 1)) * ∑ m, ‖x m‖ ^ 2 := by
  let E (m n : ι) : ℂ := ((1 / Real.sin (k * ((idx m : ℝ) - (idx n : ℝ))) -
    1 / (k * ((idx m : ℝ) - (idx n : ℝ))) : ℝ) : ℂ)
  have hE (m n : ι) (hmn : m ≠ n) : ‖E m n‖ ≤ 1 := by
    have hd : (idx m : ℝ) - (idx n : ℝ) ≠ 0 := by
      intro he
      apply hmn
      apply hinj
      exact_mod_cast (sub_eq_zero.mp he)
    simpa only [E, Complex.norm_real, Real.norm_eq_abs] using
      abs_cosecant_sub_inv_le_one _ (mul_ne_zero hk.ne' hd) (hwidth m n)
  have hsplit : (∑ m, ∑ n ∈ univ.erase m, star (x m) *
      ((1 / Real.sin (k * ((idx m : ℝ) - (idx n : ℝ))) : ℝ) : ℂ) * x n) =
      ((1 / k : ℝ) : ℂ) * (∑ m, ∑ n ∈ univ.erase m, star (x m) *
        ((1 / ((idx m : ℝ) - (idx n : ℝ)) : ℝ) : ℂ) * x n) +
      (∑ m, ∑ n ∈ univ.erase m, star (x m) * E m n * x n) := by
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro n hn
    dsimp [E]
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hsplit]
  apply (norm_add_le _ _).trans
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hk)]
  calc
    _ ≤ (1 / k) * ((7 / 2 : ℝ) * ∑ m, ‖x m‖ ^ 2) +
        ((Fintype.card ι : ℝ) - 1) * ∑ m, ‖x m‖ ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left (integer_hilbert_sum_bound idx hinj x)
        (by positivity)) (bounded_kernel_error E hE x)
    _ = _ := by ring

/-- The sine-kernel bound in the unit-numerator half-block regime, with
the precise budget required for the subsequent exponential Gram estimate. -/
theorem unit_cosecant_block_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (q h : ℝ) (hq : 100 ≤ q)
    (hlo : (q - 1) / q ^ 2 ≤ h) (hhi : h ≤ (q + 1) / q ^ 2)
    (hwidth : ∀ m n, |(idx m : ℝ) - (idx n : ℝ)| ≤ q / 2)
    (hcard : (Fintype.card ι : ℝ) - 1 ≤ q / 2) (x : ι → ℂ) :
    ‖∑ m, ∑ n ∈ univ.erase m, star (x m) *
      ((1 / Real.sin ((Real.pi * h) * ((idx m : ℝ) - (idx n : ℝ))) : ℝ) : ℂ) * x n‖ ≤
      (2 * q - 1) * ∑ m, ‖x m‖ ^ 2 := by
  have hh : 0 < h := lt_of_lt_of_le (div_pos (by linarith) (by positivity)) hlo
  have hb := cosecant_quadratic_bound idx hinj (Real.pi * h) (mul_pos Real.pi_pos hh)
    (fun m n => unit_kernel_angle q h _ hq hh.le hhi (hwidth m n)) x
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (sum_nonneg fun m hm => sq_nonneg _)
  have hc := unit_kernel_constant q h (by linarith) hlo
  linarith

/-- The difference of two phase-conjugated cosecant forms retains the same
bound after division by 2i. This is the off-diagonal geometric-sum pattern. -/
theorem unit_cosecant_phase_difference {ι : Type*} [Fintype ι] [DecidableEq ι]
    (idx : ι → ℤ) (hinj : Function.Injective idx) (q h : ℝ) (hq : 100 ≤ q)
    (hlo : (q - 1) / q ^ 2 ≤ h) (hhi : h ≤ (q + 1) / q ^ 2)
    (hwidth : ∀ m n, |(idx m : ℝ) - (idx n : ℝ)| ≤ q / 2)
    (hcard : (Fintype.card ι : ℝ) - 1 ≤ q / 2)
    (p r x : ι → ℂ) (hp : ∀ j, ‖p j‖ = 1) (hr : ∀ j, ‖r j‖ = 1) :
    ‖∑ m, ∑ n ∈ univ.erase m, star (x m) *
      ((star (p m) * p n - star (r m) * r n) / (2 * Complex.I)) *
      ((1 / Real.sin ((Real.pi * h) * ((idx m : ℝ) - (idx n : ℝ))) : ℝ) : ℂ) * x n‖ ≤
      (2 * q - 1) * ∑ m, ‖x m‖ ^ 2 := by
  let Q (v : ι → ℂ) : ℂ := ∑ m, ∑ n ∈ univ.erase m, star (v m * x m) *
    ((1 / Real.sin ((Real.pi * h) * ((idx m : ℝ) - (idx n : ℝ))) : ℝ) : ℂ) * (v n * x n)
  have hQ (v : ι → ℂ) (hv : ∀ j, ‖v j‖ = 1) :
      ‖Q v‖ ≤ (2 * q - 1) * ∑ m, ‖x m‖ ^ 2 := by
    have hb := unit_cosecant_block_bound idx hinj q h hq hlo hhi hwidth hcard
      (fun j => v j * x j)
    simpa only [Q, norm_mul, hv, one_mul] using hb
  have he : (∑ m, ∑ n ∈ univ.erase m, star (x m) *
      ((star (p m) * p n - star (r m) * r n) / (2 * Complex.I)) *
      ((1 / Real.sin ((Real.pi * h) * ((idx m : ℝ) - (idx n : ℝ))) : ℝ) : ℂ) * x n) =
      (Q p - Q r) / (2 * Complex.I) := by
    dsimp [Q]
    simp only [sum_div, ← sum_sub_distrib]
    apply sum_congr rfl
    intro m hm
    apply sum_congr rfl
    intro n hn
    simp only [map_mul]
    ring
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [he, norm_div, norm_mul, Complex.norm_I, htwo, mul_one]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have hb := (norm_sub_le (Q p) (Q r)).trans (add_le_add (hQ p hp) (hQ r hr))
  nlinarith

end TaoFivePrimes
