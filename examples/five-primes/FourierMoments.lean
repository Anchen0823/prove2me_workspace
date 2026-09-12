import Definitions.Def_TaoFivePrimes_ArcSplit
import Mathlib

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace TaoFourierIdentity

/-! Finite Fourier correlation identities for the local L2 argument in
Tao, arXiv:1201.6656v4, Proposition 4.8. These identities have no
number-theoretic hypotheses; prime-mass and tail estimates remain separate. -/

theorem integral_character_correlation (m n : ℤ) :
    (∫ α : AddCircle (1 : ℝ), fourier m α * conj (fourier n α)
      ∂AddCircle.haarAddCircle) = if n = m then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp
    (orthonormal_fourier (T := (1 : ℝ)))) n m
  rw [ContinuousMap.inner_toLp] at h
  exact h

theorem continuous_fourierPolynomial {ι : Type*} (s : Finset ι)
    (a : ι → ℂ) (k : ι → ℤ) : Continuous (fourierPolynomial s a k) := by
  unfold fourierPolynomial
  fun_prop

theorem integral_fourierPolynomial_correlation {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℂ) (k : ι → ℤ) (hk : Function.Injective k) :
    (∫ α : AddCircle (1 : ℝ),
      fourierPolynomial s a k α * conj (fourierPolynomial s b k α)
      ∂AddCircle.haarAddCircle) = ∑ i ∈ s, a i * conj (b i) := by
  classical
  simp only [fourierPolynomial, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum]
    · simp_rw [show ∀ j (α : AddCircle (1 : ℝ)), a j * fourier (k j) α *
          (conj (b i) * conj (fourier (k i) α)) =
          (a j * conj (b i)) * (fourier (k j) α * conj (fourier (k i) α)) by
        intros; ring]
      simp_rw [integral_const_mul, integral_character_correlation, hk.eq_iff]
      simp [hi]
    · intro j hj
      exact (by fun_prop : Continuous (fun α : AddCircle (1 : ℝ) =>
        a j * fourier (k j) α * (conj (b i) * conj (fourier (k i) α)))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  · intro i hi
    exact (by fun_prop : Continuous (fun α : AddCircle (1 : ℝ) =>
      ∑ j ∈ s, a j * fourier (k j) α *
        (conj (b i) * conj (fourier (k i) α)))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)

theorem integral_fourierPolynomial_norm_sq {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ) (k : ι → ℤ) (hk : Function.Injective k) :
    (∫ α : AddCircle (1 : ℝ), ‖fourierPolynomial s a k α‖ ^ 2
      ∂AddCircle.haarAddCircle) = ∑ i ∈ s, ‖a i‖ ^ 2 := by
  have h := integral_fourierPolynomial_correlation s a a k hk
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  rw [integral_complex_ofReal] at h
  simpa [← Complex.ofReal_pow] using congrArg Complex.re h

end TaoFourierIdentity

namespace TaoFivePrimes

/-- The exact quadratic prime mass appearing in the local L2 argument. -/
theorem S1_cutoff_correlation (x : ℕ) :
    (∫ α : AddCircle (1 : ℝ), S1 x α *
      conj (TaoFourierIdentity.fourierPolynomial (Finset.range (x + 1))
        (fun n ↦ (eta1 ((n : ℝ) / x) : ℂ)) (fun n ↦ (n : ℤ)) α)
      ∂AddCircle.haarAddCircle) =
    ((∑ n ∈ Finset.range (x + 1),
      siftedVonMangoldt x n * eta1 ((n : ℝ) / x) ^ 2 : ℝ) : ℂ) := by
  unfold S1
  rw [TaoFourierIdentity.integral_fourierPolynomial_correlation _ _ _ _ Nat.cast_injective]
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Complex.conj_ofReal]
  ring

end TaoFivePrimes
