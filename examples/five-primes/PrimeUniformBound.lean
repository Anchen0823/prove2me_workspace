import examples.«five-primes».FourierMoments

open MeasureTheory
open scoped BigOperators ArithmeticFunction.vonMangoldt ComplexConjugate

namespace TaoFivePrimes

theorem prime_mass_le_six_mul (x : ℕ) :
    (∑ n ∈ Finset.range (x + 1), (Λ n : ℝ)) ≤ 6 * (x : ℝ) := by
  have hp := Chebyshev.psi_le_const_mul_self (show (0 : ℝ) ≤ x by positivity)
  have heq : Chebyshev.psi (x : ℝ) = ∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) := by
    rw [Chebyshev.psi_eq_sum_Icc]
    have hs : Finset.Icc 0 x = Finset.range (x + 1) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_range]
      omega
    simpa only [Nat.floor_natCast, hs]
  have hlog : Real.log 4 ≤ 2 := by
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have he : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith
  rw [heq] at hp
  apply hp.trans
  gcongr
  linarith

theorem sifted_weight_bounds (x n : ℕ) :
    0 ≤ siftedVonMangoldt x n ∧ siftedVonMangoldt x n ≤ Λ n := by
  unfold siftedVonMangoldt
  split_ifs
  · exact ⟨ArithmeticFunction.vonMangoldt_nonneg, le_rfl⟩
  · exact ⟨le_rfl, ArithmeticFunction.vonMangoldt_nonneg⟩

theorem S1_norm_le_prime_mass (x : ℕ) (α : AddCircle (1 : ℝ)) :
    ‖S1 x α‖ ≤ ∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) := by
  unfold S1 TaoFourierIdentity.fourierPolynomial
  apply le_trans (norm_sum_le _ _)
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul, show ‖fourier (n : ℤ) α‖ = 1 from Circle.norm_coe _, mul_one,
    Complex.norm_real, Real.norm_of_nonneg (by
      apply mul_nonneg (sifted_weight_bounds x n).1
      exact le_max_left _ _)]
  have he : eta1 ((n : ℝ) / x) ≤ 1 := by
    unfold eta1
    have hd : 0 ≤ Metric.infDist ((n : ℝ) / x) (Set.Icc (1 / 5 : ℝ) (4 / 5)) :=
      Metric.infDist_nonneg
    apply max_le (by norm_num)
    linarith
  calc
    _ ≤ siftedVonMangoldt x n * 1 :=
      mul_le_mul_of_nonneg_left he (sifted_weight_bounds x n).1
    _ ≤ Λ n := by simpa using (sifted_weight_bounds x n).2

theorem norm_correlation_le_uniform (f g : C(AddCircle (1 : ℝ), ℂ))
    (E : Set (AddCircle (1 : ℝ))) (C : ℝ) (hC : ∀ α, ‖f α‖ ≤ C) :
    ‖∫ α in E, f α * conj (g α) ∂AddCircle.haarAddCircle‖ ≤
      C * ∫ α in E, ‖g α‖ ∂AddCircle.haarAddCircle := by
  calc
    _ ≤ ∫ α in E, ‖f α * conj (g α)‖ ∂AddCircle.haarAddCircle :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ α in E, C * ‖g α‖ ∂AddCircle.haarAddCircle := by
      apply integral_mono
      · exact (by fun_prop : Continuous (fun α => ‖f α * conj (g α)‖)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · exact (by fun_prop : Continuous (fun α => C * ‖g α‖)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · intro α
        dsimp only
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_right (hC α) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

end TaoFivePrimes
