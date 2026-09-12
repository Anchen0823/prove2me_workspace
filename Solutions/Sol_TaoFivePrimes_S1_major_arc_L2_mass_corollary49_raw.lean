import Mathlib

import Definitions.Def_TaoFivePrimes_ArcSplit

import Theorems.Thm_TaoFivePrimes_eta1_quadratic_prime_mass

import Theorems.Thm_TaoFivePrimes_eta1_complementary_correlation


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



open MeasureTheory
open scoped ComplexConjugate

namespace TaoLocalL2

/-! The functional-analytic step in Proposition 4.8 of
Tao, arXiv:1201.6656v4. The restricted measure will be the major arc. -/

theorem norm_toLp_sq {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : C(X, ℂ)) :
    ‖ContinuousMap.toLp 2 μ ℂ f‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂μ := by
  have h := ContinuousMap.inner_toLp μ f f
  rw [inner_self_eq_norm_sq_to_K] at h
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  rw [integral_complex_ofReal] at h
  simpa [← Complex.ofReal_pow] using congrArg Complex.re h


theorem correlation_sq_le {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f g : C(X, ℂ)) :
    ‖∫ t, f t * conj (g t) ∂μ‖ ^ 2 ≤
      (∫ t, ‖f t‖ ^ 2 ∂μ) * (∫ t, ‖g t‖ ^ 2 ∂μ) := by
  rw [← ContinuousMap.inner_toLp μ g f]
  calc
    ‖inner ℂ (ContinuousMap.toLp 2 μ ℂ g) (ContinuousMap.toLp 2 μ ℂ f)‖ ^ 2
        ≤ (‖ContinuousMap.toLp 2 μ ℂ g‖ * ‖ContinuousMap.toLp 2 μ ℂ f‖) ^ 2 := by
          gcongr
          exact norm_inner_le_norm _ _
    _ = _ := by rw [mul_pow, norm_toLp_sq, norm_toLp_sq, mul_comm]

/-- A lower bound from a global correlation, a bound on its complementary
arc, and the global energy of the test function. -/
theorem local_energy_lower_bound
    (f g : C(AddCircle (1 : ℝ), ℂ)) (E : Set (AddCircle (1 : ℝ)))
    (hE : MeasurableSet E) (M δ D : ℝ) (hδ : 0 ≤ δ) (hδM : δ ≤ M)
    (hD : 0 < D)
    (hmass : (∫ t, f t * conj (g t) ∂AddCircle.haarAddCircle) = (M : ℂ))
    (htail : ‖∫ t in Eᶜ, f t * conj (g t) ∂AddCircle.haarAddCircle‖ ≤ δ)
    (henergy : (∫ t, ‖g t‖ ^ 2 ∂AddCircle.haarAddCircle) ≤ D) :
    (M - δ) ^ 2 / D ≤ ∫ t in E, ‖f t‖ ^ 2 ∂AddCircle.haarAddCircle := by
  have hint : Integrable (fun t => f t * conj (g t)) AddCircle.haarAddCircle :=
    (by fun_prop : Continuous (fun t => f t * conj (g t))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsplit := integral_add_compl hE hint
  rw [hmass] at hsplit
  have htriangle := norm_add_le
    (∫ t in E, f t * conj (g t) ∂AddCircle.haarAddCircle)
    (∫ t in Eᶜ, f t * conj (g t) ∂AddCircle.haarAddCircle)
  rw [hsplit, Complex.norm_real, Real.norm_of_nonneg (hδ.trans hδM)] at htriangle
  have hlower : M - δ ≤ ‖∫ t in E, f t * conj (g t) ∂AddCircle.haarAddCircle‖ := by
    linarith
  have hcs := correlation_sq_le (AddCircle.haarAddCircle.restrict E) f g
  have hgle : (∫ t in E, ‖g t‖ ^ 2 ∂AddCircle.haarAddCircle) ≤ D := by
    apply le_trans (setIntegral_le_integral ?_ ?_) henergy
    · exact (by fun_prop : Continuous (fun t => ‖g t‖ ^ 2)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · exact Filter.Eventually.of_forall (fun _ => sq_nonneg _)
  have hfnonneg : 0 ≤ ∫ t in E, ‖f t‖ ^ 2 ∂AddCircle.haarAddCircle :=
    integral_nonneg (fun _ => sq_nonneg _)
  apply (div_le_iff₀ hD).2
  calc
    (M - δ) ^ 2 ≤ ‖∫ t in E, f t * conj (g t) ∂AddCircle.haarAddCircle‖ ^ 2 := by
      gcongr
    _ ≤ _ := hcs.trans (mul_le_mul_of_nonneg_left hgle hfnonneg)

/-- Keep the normalization and denominator loss explicit when specializing
the local energy estimate to the trapezoidal cutoff. -/
theorem normalized_major_arc_arithmetic (x ε A : ℝ) (hx : 15000 ≤ x)
    (hA : 0 ≤ A)
    (hlocal : (0.99 * ((2 / 3 : ℝ) * (1 + ε) * x)) ^ 2 ≤
      A * ((2 / 3 : ℝ) * x + 1)) :
    0.999 * (0.99 * (1 + ε)) ^ 2 * x ≤ (3 / 2 : ℝ) * A := by
  have hxpos : 0 < x := by linarith
  have hdenom : 0.999 * ((2 / 3 : ℝ) * x + 1) ≤ (2 / 3 : ℝ) * x := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hlocal (by norm_num : (0 : ℝ) ≤ 0.999)
  have hupper := mul_le_mul_of_nonneg_left hdenom hA
  apply (mul_le_mul_iff_left₀ hxpos).mp
  nlinarith

/-- The direct nonsmooth quadrature estimate loses at most 20. This still
preserves the target's 0.999 coefficient when x >= 30000. -/
theorem normalized_major_arc_arithmetic_twenty (x ε A : ℝ) (hx : 30000 ≤ x)
    (hA : 0 ≤ A)
    (hlocal : (0.99 * ((2 / 3 : ℝ) * (1 + ε) * x)) ^ 2 ≤
      A * ((2 / 3 : ℝ) * x + 20)) :
    0.999 * (0.99 * (1 + ε)) ^ 2 * x ≤ (3 / 2 : ℝ) * A := by
  have hxpos : 0 < x := by linarith
  have hdenom : 0.999 * ((2 / 3 : ℝ) * x + 20) ≤ (2 / 3 : ℝ) * x := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hlocal (by norm_num : (0 : ℝ) ≤ 0.999)
  have hupper := mul_le_mul_of_nonneg_left hdenom hA
  apply (mul_le_mul_iff_left₀ hxpos).mp
  nlinarith

end TaoLocalL2



open MeasureTheory Set intervalIntegral

namespace TaoFivePrimes

private theorem integral_linear (a b c : ℝ) :
    (∫ t in a..b, c * t) = c * ((b ^ 2 - a ^ 2) / 2) := by
  calc
    _ = c * (∫ t in a..b, t) := intervalIntegral.integral_const_mul c (fun t : ℝ => t)
    _ = _ := by rw [integral_id]

theorem eta1_bounds (t : ℝ) : 0 ≤ eta1 t ∧ eta1 t ≤ 1 := by
  constructor
  · exact le_max_left _ _
  · unfold eta1
    have hd : 0 ≤ Metric.infDist t (Set.Icc (1 / 5 : ℝ) (4 / 5)) := Metric.infDist_nonneg
    exact max_le (by norm_num) (by linarith)

@[fun_prop] theorem eta1_continuous : Continuous eta1 := by
  unfold eta1
  fun_prop

theorem eta1_left (t : ℝ) (ht : t ≤ 1 / 5) :
    eta1 t = max 0 (10 * t - 1) := by
  have hd : Metric.infDist t (Set.Icc (1 / 5 : ℝ) (4 / 5)) = 1 / 5 - t := by
    apply le_antisymm
    · have h := Metric.infDist_le_dist_of_mem
        (x := t) (s := Set.Icc (1 / 5 : ℝ) (4 / 5))
        (y := (1 / 5 : ℝ)) (by constructor <;> norm_num)
      rw [Real.dist_eq, abs_of_nonpos (by linarith : t - 1 / 5 ≤ 0)] at h
      linarith
    · apply (Metric.le_infDist (by exact ⟨1 / 5, by constructor <;> norm_num⟩)).2
      intro y hy
      rw [Real.dist_eq, abs_of_nonpos (by linarith [hy.1] : t - y ≤ 0)]
      linarith [hy.1]
  unfold eta1
  rw [hd]
  congr 1
  ring

theorem eta1_middle (t : ℝ) (ht : t ∈ Set.Icc (1 / 5 : ℝ) (4 / 5)) :
    eta1 t = 1 := by
  unfold eta1
  rw [Metric.infDist_zero_of_mem ht]
  norm_num

theorem eta1_right (t : ℝ) (ht : 4 / 5 ≤ t) :
    eta1 t = max 0 (9 - 10 * t) := by
  have hd : Metric.infDist t (Set.Icc (1 / 5 : ℝ) (4 / 5)) = t - 4 / 5 := by
    apply le_antisymm
    · have h := Metric.infDist_le_dist_of_mem
        (x := t) (s := Set.Icc (1 / 5 : ℝ) (4 / 5))
        (y := (4 / 5 : ℝ)) (by constructor <;> norm_num)
      simpa [Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ t - 4 / 5)] using h
    · apply (Metric.le_infDist (by exact ⟨1 / 5, by constructor <;> norm_num⟩)).2
      intro y hy
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hy.2] : 0 ≤ t - y)]
      linarith [hy.2]
  unfold eta1
  rw [hd]
  congr 1
  ring

theorem eta1_sq_intervalIntegral : (∫ t in (0 : ℝ)..1, eta1 t ^ 2) = 2 / 3 := by
  have hint (a b : ℝ) : IntervalIntegrable (fun t => eta1 t ^ 2) volume a b :=
    (eta1_continuous.pow 2).intervalIntegrable _ _
  have h0 : (∫ t in (0 : ℝ)..(1 / 10), eta1 t ^ 2) = 0 := by
    calc
      _ = ∫ t in (0 : ℝ)..(1 / 10), (0 : ℝ) := by
        apply integral_congr
        intro t ht
        dsimp only
        rw [uIcc_of_le (by norm_num)] at ht
        rw [eta1_left t (by linarith [ht.2]), max_eq_left (by linarith [ht.2])]
        norm_num
      _ = 0 := by simp
  have h1 : (∫ t in (1 / 10 : ℝ)..(1 / 5), eta1 t ^ 2) = 1 / 30 := by
    calc
      _ = ∫ t in (1 / 10 : ℝ)..(1 / 5), (100 * t ^ 2 - 20 * t + 1) := by
        apply integral_congr
        intro t ht
        dsimp only
        rw [uIcc_of_le (by norm_num)] at ht
        rw [eta1_left t ht.2, max_eq_right (by linarith [ht.1])]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
          intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)]
        norm_num [integral_linear, intervalIntegral.integral_const_mul, integral_pow, integral_id]
  have h2 : (∫ t in (1 / 5 : ℝ)..(4 / 5), eta1 t ^ 2) = 3 / 5 := by
    calc
      _ = ∫ t in (1 / 5 : ℝ)..(4 / 5), (1 : ℝ) := by
        apply integral_congr
        intro t ht
        dsimp only
        rw [uIcc_of_le (by norm_num)] at ht
        rw [eta1_middle t ht]
        norm_num
      _ = _ := by norm_num
  have h3 : (∫ t in (4 / 5 : ℝ)..(9 / 10), eta1 t ^ 2) = 1 / 30 := by
    calc
      _ = ∫ t in (4 / 5 : ℝ)..(9 / 10), (81 - 180 * t + 100 * t ^ 2) := by
        apply integral_congr
        intro t ht
        dsimp only
        rw [uIcc_of_le (by norm_num)] at ht
        rw [eta1_right t ht.1, max_eq_right (by linarith [ht.2])]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),
          intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)]
        norm_num [integral_linear, intervalIntegral.integral_const_mul, integral_pow, integral_id]
  have h4 : (∫ t in (9 / 10 : ℝ)..1, eta1 t ^ 2) = 0 := by
    calc
      _ = ∫ t in (9 / 10 : ℝ)..1, (0 : ℝ) := by
        apply integral_congr
        intro t ht
        dsimp only
        rw [uIcc_of_le (by norm_num)] at ht
        rw [eta1_right t (by linarith [ht.1]), max_eq_left (by linarith [ht.1])]
        norm_num
      _ = 0 := by simp
  have hsum := integral_add_adjacent_intervals (hint 0 (1 / 10)) (hint (1 / 10) 1)
  rw [← integral_add_adjacent_intervals (hint (1 / 10) (1 / 5)) (hint (1 / 5) 1),
    ← integral_add_adjacent_intervals (hint (1 / 5) (4 / 5)) (hint (4 / 5) 1),
    ← integral_add_adjacent_intervals (hint (4 / 5) (9 / 10)) (hint (9 / 10) 1),
    h0, h1, h2, h3, h4] at hsum
  linarith

theorem eta1_le_add_dist (u v : ℝ) : eta1 u ≤ eta1 v + 10 * |u - v| := by
  have hdist := Metric.infDist_le_infDist_add_dist
    (s := Set.Icc (1 / 5 : ℝ) (4 / 5)) (x := v) (y := u)
  rw [Real.dist_eq, abs_sub_comm v u] at hdist
  have hv := le_max_right (0 : ℝ)
    (1 - 10 * Metric.infDist v (Set.Icc (1 / 5 : ℝ) (4 / 5)))
  change 1 - 10 * Metric.infDist v _ ≤ eta1 v at hv
  unfold eta1
  apply max_le
  · change 0 ≤ eta1 v + 10 * |u - v|
    have hv0 := (eta1_bounds v).1
    positivity
  · change 1 - 10 * Metric.infDist u _ ≤ eta1 v + 10 * |u - v|
    linarith

theorem eta1_sq_le_add_dist (u v : ℝ) :
    eta1 u ^ 2 ≤ eta1 v ^ 2 + 20 * |u - v| := by
  obtain ⟨hu0, hu1⟩ := eta1_bounds u
  obtain ⟨hv0, hv1⟩ := eta1_bounds v
  have h := mul_le_mul_of_nonneg_right (eta1_le_add_dist u v)
    (add_nonneg hu0 hv0)
  have herror := mul_nonneg (abs_nonneg (u - v)) (show 0 ≤ 2 - eta1 u - eta1 v by linarith)
  nlinarith

/-- A direct Lipschitz quadrature bound for the literal nonsmooth cutoff.
The additive constant 20 is ample for the raw target's x >= 10^9 range. -/
theorem eta1_discrete_square_sum_le (x : ℕ) (hx : 0 < x) :
    (∑ n ∈ Finset.range (x + 1), eta1 ((n : ℝ) / x) ^ 2) ≤ (2 / 3 : ℝ) * x + 20 := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hg : Continuous (fun t : ℝ => eta1 (t / x) ^ 2 + 20 / x) := by
    fun_prop
  have hsum := sum_Ico_le_integral_of_le (f := fun t : ℝ => eta1 (t / x) ^ 2)
    (g := fun t : ℝ => eta1 (t / x) ^ 2 + 20 / x) (a := 0) (b := x)
    (Nat.zero_le x) (by
      intro i hi t ht
      have hd : |(i : ℝ) / x - t / x| ≤ 1 / x := by
        rw [← sub_div, abs_div, abs_of_pos hxR,
          abs_of_nonpos (by linarith [ht.1] : (i : ℝ) - t ≤ 0)]
        apply (div_le_div_iff_of_pos_right hxR).2
        have htt := ht.2
        push_cast at htt
        linarith
      have h := eta1_sq_le_add_dist ((i : ℝ) / x) (t / x)
      have hd20 : 20 * |(i : ℝ) / x - t / x| ≤ 20 / x := by
        calc
          _ ≤ (20 : ℝ) * (1 / (x : ℝ)) := mul_le_mul_of_nonneg_left hd (by norm_num)
          _ = _ := by ring
      linarith) ((hg.integrableOn_Icc).mono_set Set.Ico_subset_Icc_self)
  have hint : (∫ t in (0 : ℝ)..x, eta1 (t / x) ^ 2 + 20 / x) =
      (2 / 3 : ℝ) * x + 20 := by
    rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)]
    rw [integral_comp_div (fun t : ℝ => eta1 t ^ 2) (ne_of_gt hxR)]
    simp [hxR.ne', eta1_sq_intervalIntegral, smul_eq_mul]
    field_simp
  have hend : eta1 ((x : ℝ) / x) = 0 := by
    rw [div_self hxR.ne', eta1_right 1 (by norm_num)]
    norm_num
  rw [Finset.sum_range_succ, hend]
  simpa [Nat.Ico_zero_eq_range, hint] using hsum

end TaoFivePrimes



open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace TaoFivePrimes

/-! A reduction with exactly two remaining analytic inputs: quadratic prime
mass and complementary correlation. The cutoff energy is proved locally. -/

theorem S1_raw_of_mass_and_tail (x : ℕ) (hx : (10 ^ 9 : ℝ) ≤ x)
    (ε : ℝ) (hε : |ε| ≤ 0.02)
    (hmass : (∑ n ∈ Finset.range (x + 1),
      siftedVonMangoldt x n * eta1 ((n : ℝ) / x) ^ 2) =
      (2 / 3 : ℝ) * (1 + ε) * x)
    (htail : ‖∫ α in (majorArc x)ᶜ, S1 x α *
      conj (TaoFourierIdentity.fourierPolynomial (Finset.range (x + 1))
        (fun n ↦ (eta1 ((n : ℝ) / x) : ℂ)) (fun n ↦ (n : ℤ)) α)
        ∂AddCircle.haarAddCircle‖ ≤
      0.01 * ((2 / 3 : ℝ) * (1 + ε) * x)) :
    0.999 * (0.99 * (1 + ε)) ^ 2 * x ≤ (3 / 2 : ℝ) *
      ∫ α in majorArc x, ‖S1 x α‖ ^ 2 ∂AddCircle.haarAddCircle := by
  let f : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨S1 x, TaoFourierIdentity.continuous_fourierPolynomial _ _ _⟩
  let g : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨TaoFourierIdentity.fourierPolynomial (Finset.range (x + 1))
      (fun n ↦ (eta1 ((n : ℝ) / x) : ℂ)) (fun n ↦ (n : ℤ)),
      TaoFourierIdentity.continuous_fourierPolynomial _ _ _⟩
  let M : ℝ := (2 / 3 : ℝ) * (1 + ε) * x
  let D : ℝ := (2 / 3 : ℝ) * x + 20
  have hxpos : (0 : ℝ) < x := by linarith
  have hM : 0 ≤ M := by
    have he := (abs_le.mp hε).1
    have hepos : 0 ≤ 1 + ε := by linarith
    dsimp [M]
    positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hE : MeasurableSet (majorArc x) := by
    exact isClosed_le continuous_norm continuous_const |>.measurableSet
  have hcorr : (∫ t, f t * conj (g t) ∂AddCircle.haarAddCircle) = (M : ℂ) := by
    change (∫ t, S1 x t * conj (TaoFourierIdentity.fourierPolynomial
      (Finset.range (x + 1)) (fun n ↦ (eta1 ((n : ℝ) / x) : ℂ))
      (fun n ↦ (n : ℤ)) t) ∂AddCircle.haarAddCircle) = (M : ℂ)
    rw [S1_cutoff_correlation, hmass]
  have henergy : (∫ t, ‖g t‖ ^ 2 ∂AddCircle.haarAddCircle) ≤ D := by
    change (∫ t, ‖TaoFourierIdentity.fourierPolynomial _ _ _ t‖ ^ 2
      ∂AddCircle.haarAddCircle) ≤ D
    rw [TaoFourierIdentity.integral_fourierPolynomial_norm_sq _ _ _ Nat.cast_injective]
    simpa [D, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      eta1_discrete_square_sum_le x (by exact_mod_cast hxpos)
  have hlocal := TaoLocalL2.local_energy_lower_bound f g (majorArc x) hE
    M (0.01 * M) D (by positivity) (by nlinarith) hD hcorr htail henergy
  have hprod := (div_le_iff₀ hD).mp hlocal
  have hprod' : (0.99 * ((2 / 3 : ℝ) * (1 + ε) * x)) ^ 2 ≤
      (∫ α in majorArc x, ‖S1 x α‖ ^ 2 ∂AddCircle.haarAddCircle) *
        ((2 / 3 : ℝ) * x + 20) := by
    change (M - 0.01 * M) ^ 2 ≤
      (∫ α in majorArc x, ‖S1 x α‖ ^ 2 ∂AddCircle.haarAddCircle) * D at hprod
    convert hprod using 1 <;> dsimp [M, D, f] <;> ring
  exact TaoLocalL2.normalized_major_arc_arithmetic_twenty (x : ℝ) ε _
    (by linarith) (integral_nonneg (fun _ => sq_nonneg _)) hprod'

end TaoFivePrimes


open MeasureTheory TaoFivePrimes
theorem solution (x : ℕ)
    (hr_lower : 1 / (2 * (x : ℝ)) ≤ T0 / (3.6 * Real.pi * (x : ℝ)))
    (hr_upper : T0 / (3.6 * Real.pi * (x : ℝ)) ≤ 1 / 2)
    (hc8 : (10 ^ 8 : ℝ) ≤ (1 / 10 : ℝ) * x)
    (hneat : (10 ^ 4 : ℝ) * (3 / 2 : ℝ) ≤ x)
    (halamo : 5 * (3 / 2 : ℝ) ≤ Real.log ((1 / 10 : ℝ) * x))
    (h10q : (10 ^ 8 : ℝ) * (9 / 4 : ℝ) ≤ x)
    (hr0b : 20 * 60 * Real.sqrt (3 / 2 : ℝ) ≤ T0 / (3.6 * Real.pi)) :
    ∃ eps : ℝ, |eps| ≤ 0.02 ∧
      0.999 * (0.99 * (1 + eps)) ^ 2 * x ≤
        (3 / 2 : ℝ) *
          ∫ alpha in majorArc x, ‖S1 x alpha‖ ^ 2 ∂AddCircle.haarAddCircle := by
  obtain ⟨ε, hε, hmass⟩ := TaoFivePrimes.eta1_quadratic_prime_mass x hc8 hneat halamo h10q
  refine ⟨ε, hε, ?_⟩
  apply TaoFivePrimes.S1_raw_of_mass_and_tail x (by linarith) ε hε hmass
  exact TaoFivePrimes.eta1_complementary_correlation x hr_lower hr_upper hc8 hneat
    halamo h10q hr0b ε hε hmass