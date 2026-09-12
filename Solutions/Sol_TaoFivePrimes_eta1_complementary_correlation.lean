import Mathlib

import Definitions.Def_TaoFivePrimes_ArcSplit

section

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

end

section

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

end

section

namespace TaoFivePrimes

/-- An exact hinge decomposition of the Section 8 trapezoid. It permits
second-difference estimates without smoothing the literal cutoff. -/
theorem eta1_hinge_decomposition (t : ℝ) :
    eta1 t = max 0 (10 * t - 1) - max 0 (10 * t - 2) -
      max 0 (10 * t - 8) + max 0 (10 * t - 9) := by
  rcases le_total t (1 / 5) with ht | ht
  · rw [eta1_left t ht]
    simp only [max_def]
    split_ifs <;> linarith
  · rcases le_total t (4 / 5) with ht' | ht'
    · rw [eta1_middle t ⟨ht, ht'⟩]
      simp only [max_def]
      split_ifs <;> linarith
    · rw [eta1_right t ht']
      simp only [max_def]
      split_ifs <;> linarith

/-- Nonnegative second differences of a hinge, for every mesh width. -/
theorem hinge_second_difference_nonneg (t h : ℝ) :
    0 ≤ max 0 (t + h) - 2 * max 0 t + max 0 (t - h) := by
  simp only [max_def]
  split_ifs <;> linarith

theorem sum_second_difference (u : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (u (n + 2) - 2 * u (n + 1) + u n)) =
      u (N + 1) - u N - u 1 + u 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- Each ramp contributes exactly its slope to the total second difference
once both ends of the mesh lie outside the transition. -/
theorem sampled_hinge_second_difference_sum (x : ℕ) (hx : 10 ≤ x)
    (b : ℝ) (hb0 : 1 ≤ b) (hb1 : b ≤ 9) :
    (∑ n ∈ Finset.range x,
      (max 0 ((10 / (x : ℝ)) * (n + 2) - b) -
        2 * max 0 ((10 / (x : ℝ)) * (n + 1) - b) +
        max 0 ((10 / (x : ℝ)) * n - b))) = 10 / (x : ℝ) := by
  have hxR : (10 : ℝ) ≤ x := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hs : (10 : ℝ) / x ≤ 1 := (div_le_one hxpos).2 hxR
  have hs0 : (0 : ℝ) ≤ 10 / x := by positivity
  have hsx : ((10 : ℝ) / x) * x = 10 := div_mul_cancel₀ _ hxpos.ne'
  have h := sum_second_difference (fun n : ℕ => max 0 ((10 / (x : ℝ)) * n - b)) x
  push_cast at h
  have hN : (10 / (x : ℝ)) * (x + 1) - b = 10 + 10 / (x : ℝ) - b := by
    rw [mul_add, hsx, mul_one]
  rw [hN, hsx, mul_one, mul_zero, zero_sub,
    max_eq_right (by linarith : 0 ≤ 10 + 10 / (x : ℝ) - b),
    max_eq_right (by linarith : 0 ≤ 10 - b),
    max_eq_left (by linarith : 10 / (x : ℝ) - b ≤ 0),
    max_eq_left (by linarith : -b ≤ 0)] at h
  linarith

/-- Total second-difference mass of the literal sampled trapezoid. -/
theorem eta1_second_difference_mass (x : ℕ) (hx : 10 ≤ x) :
    (∑ n ∈ Finset.range x,
      |eta1 (((n : ℝ) + 2) / x) - 2 * eta1 (((n : ℝ) + 1) / x) +
        eta1 ((n : ℝ) / x)|) ≤ 40 / (x : ℝ) := by
  let D (b : ℝ) (n : ℕ) : ℝ :=
    max 0 ((10 / (x : ℝ)) * (n + 2) - b) -
      2 * max 0 ((10 / (x : ℝ)) * (n + 1) - b) +
      max 0 ((10 / (x : ℝ)) * n - b)
  have hD (b : ℝ) (n : ℕ) : 0 ≤ D b n := by
    have h := hinge_second_difference_nonneg
      ((10 / (x : ℝ)) * (n + 1) - b) (10 / (x : ℝ))
    have hp : (10 / (x : ℝ)) * (n + 1) - b + 10 / (x : ℝ) =
        (10 / (x : ℝ)) * (n + 2) - b := by ring
    have hm : (10 / (x : ℝ)) * (n + 1) - b - 10 / (x : ℝ) =
        (10 / (x : ℝ)) * n - b := by ring
    rw [hp, hm] at h
    exact h
  have hsum (b : ℝ) (hb0 : 1 ≤ b) (hb1 : b ≤ 9) :
      (∑ n ∈ Finset.range x, D b n) = 10 / (x : ℝ) :=
    sampled_hinge_second_difference_sum x hx b hb0 hb1
  have hsamp (t : ℝ) : eta1 (t / x) =
      max 0 ((10 / (x : ℝ)) * t - 1) - max 0 ((10 / (x : ℝ)) * t - 2) -
        max 0 ((10 / (x : ℝ)) * t - 8) + max 0 ((10 / (x : ℝ)) * t - 9) := by
    rw [eta1_hinge_decomposition]
    rw [show 10 * (t / (x : ℝ)) = (10 / (x : ℝ)) * t by ring]
  calc
    _ ≤ ∑ n ∈ Finset.range x, (D 1 n + D 2 n + D 8 n + D 9 n) := by
      apply Finset.sum_le_sum
      intro n hn
      have hlin : eta1 (((n : ℝ) + 2) / x) - 2 * eta1 (((n : ℝ) + 1) / x) +
          eta1 ((n : ℝ) / x) = D 1 n - D 2 n - D 8 n + D 9 n := by
        simp only [hsamp]
        dsimp [D]
        ring
      rw [hlin]
      apply abs_le.mpr
      constructor <;> linarith [hD 1 n, hD 2 n, hD 8 n, hD 9 n]
    _ = _ := by
      simp only [Finset.sum_add_distrib,
        hsum 1 (by norm_num) (by norm_num), hsum 2 (by norm_num) (by norm_num),
        hsum 8 (by norm_num) (by norm_num), hsum 9 (by norm_num) (by norm_num)]
      ring

end TaoFivePrimes

end

section

open scoped BigOperators

namespace TaoFiniteDifference

/-! Discrete Fourier differentiation for the complementary-correlation
estimate. Integer-indexed finite support keeps all boundary terms explicit. -/

noncomputable def transform (a : ℤ →₀ ℂ) (α : AddCircle (1 : ℝ)) : ℂ :=
  a.sum (fun n c => c * fourier n α)

noncomputable def shift (a : ℤ →₀ ℂ) : ℤ →₀ ℂ := a.mapDomain (fun n => n + 1)

noncomputable def difference (a : ℤ →₀ ℂ) : ℤ →₀ ℂ := a - shift a

theorem transform_sub (a b : ℤ →₀ ℂ) (α : AddCircle (1 : ℝ)) :
    transform (a - b) α = transform a α - transform b α := by
  exact Finsupp.sum_sub_index (fun _ _ _ => sub_mul _ _ _)

theorem transform_shift (a : ℤ →₀ ℂ) (α : AddCircle (1 : ℝ)) :
    transform (shift a) α = transform a α * fourier 1 α := by
  unfold transform shift
  rw [Finsupp.sum_mapDomain_index (by intros; simp) (by intros; simp [add_mul])]
  simp only [fourier_add, Finsupp.sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem transform_difference (a : ℤ →₀ ℂ) (α : AddCircle (1 : ℝ)) :
    transform (difference a) α = (1 - fourier 1 α) * transform a α := by
  unfold difference
  rw [transform_sub, transform_shift]
  ring

theorem transform_second_difference (a : ℤ →₀ ℂ) (α : AddCircle (1 : ℝ)) :
    transform (difference (difference a)) α =
      (1 - fourier 1 α) ^ 2 * transform a α := by
  rw [transform_difference, transform_difference]
  ring

theorem norm_transform_le (a : ℤ →₀ ℂ) (α : AddCircle (1 : ℝ)) :
    ‖transform a α‖ ≤ ∑ n ∈ a.support, ‖a n‖ := by
  unfold transform Finsupp.sum
  calc
    _ ≤ ∑ n ∈ a.support, ‖a n * fourier n α‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, show ‖fourier n α‖ = 1 from Circle.norm_coe _]
      simp

theorem second_difference_decay (a : ℤ →₀ ℂ) (α : AddCircle (1 : ℝ)) :
    ‖1 - fourier 1 α‖ ^ 2 * ‖transform a α‖ ≤
      ∑ n ∈ (difference (difference a)).support, ‖difference (difference a) n‖ := by
  have h := norm_transform_le (difference (difference a)) α
  rw [transform_second_difference, norm_mul, norm_pow] at h
  exact h

end TaoFiniteDifference

end

section

open scoped BigOperators

namespace TaoFiniteDifference

theorem shift_apply (a : ℤ →₀ ℂ) (n : ℤ) : shift a n = a (n - 1) := by
  have h := Finsupp.mapDomain_apply (f := fun k : ℤ => k + 1)
    (by intro i j hij; exact add_right_cancel hij) a (n - 1)
  simpa [shift] using h

theorem difference_apply (a : ℤ →₀ ℂ) (n : ℤ) :
    difference a n = a n - a (n - 1) := by
  simp [difference, shift_apply]

theorem second_difference_apply (a : ℤ →₀ ℂ) (n : ℤ) :
    difference (difference a) n = a n - 2 * a (n - 1) + a (n - 2) := by
  rw [difference_apply, difference_apply, difference_apply]
  rw [show n - 1 - 1 = n - 2 by omega]
  ring

end TaoFiniteDifference

namespace TaoFivePrimes

private theorem norm_real_second_difference (a b c : ℝ) :
    ‖(a : ℂ) - 2 * (b : ℂ) + (c : ℂ)‖ = |a - 2 * b + c| := by
  have h : (a : ℂ) - 2 * (b : ℂ) + (c : ℂ) = ((a - 2 * b + c : ℝ) : ℂ) := by
    push_cast
    <;> ring
  rw [h, Complex.norm_real, Real.norm_eq_abs]

theorem eta1_zero_of_nonpos (t : ℝ) (ht : t ≤ 0) : eta1 t = 0 := by
  rw [eta1_left t (by linarith), max_eq_left (by linarith)]

theorem eta1_zero_of_one_le (t : ℝ) (ht : 1 ≤ t) : eta1 t = 0 := by
  rw [eta1_right t (by linarith), max_eq_left (by linarith)]

theorem eta1_nonzero_interval (t : ℝ) (ht : eta1 t ≠ 0) : 0 < t ∧ t < 1 := by
  constructor
  · by_contra h
    exact ht (eta1_zero_of_nonpos t (by linarith))
  · by_contra h
    exact ht (eta1_zero_of_one_le t (by linarith))

theorem sampled_cutoff_support (x : ℕ) (hx : 0 < x) (n : ℤ)
    (hn : (eta1 ((n : ℝ) / x) : ℂ) ≠ 0) :
    n ∈ (Finset.range (x + 1)).image (fun k : ℕ => (k : ℤ)) := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have ht := eta1_nonzero_interval ((n : ℝ) / x) (by exact_mod_cast hn)
  have hlo : (0 : ℝ) < n := by
    have h := (lt_div_iff₀ hxR).mp ht.1
    linarith
  have hhi : (n : ℝ) < x := by
    have h := (div_lt_iff₀ hxR).mp ht.2
    linarith
  have hn0 : 0 ≤ n := by exact_mod_cast (le_of_lt hlo)
  have hnx : n < x := by exact_mod_cast hhi
  apply Finset.mem_image.mpr
  refine ⟨n.toNat, ?_, ?_⟩
  · simp only [Finset.mem_range]
    omega
  · omega

noncomputable def sampledCutoff (x : ℕ) (hx : 0 < x) : ℤ →₀ ℂ :=
  Finsupp.onFinset ((Finset.range (x + 1)).image (fun k : ℕ => (k : ℤ)))
    (fun n => (eta1 ((n : ℝ) / x) : ℂ)) (sampled_cutoff_support x hx)

@[simp] theorem sampledCutoff_apply (x : ℕ) (hx : 0 < x) (n : ℤ) :
    sampledCutoff x hx n = (eta1 ((n : ℝ) / x) : ℂ) := rfl

theorem sampledCutoff_transform (x : ℕ) (hx : 0 < x) (α : AddCircle (1 : ℝ)) :
    TaoFiniteDifference.transform (sampledCutoff x hx) α =
      TaoFourierIdentity.fourierPolynomial (Finset.range (x + 1))
        (fun n ↦ (eta1 ((n : ℝ) / x) : ℂ)) (fun n ↦ (n : ℤ)) α := by
  classical
  unfold TaoFiniteDifference.transform sampledCutoff
  rw [Finsupp.sum_onFinset _ _ _ _ (by intros; simp)]
  rw [Finset.sum_image]
  · simp [TaoFourierIdentity.fourierPolynomial]
  · intro i hi j hj hij
    change (i : ℤ) = (j : ℤ) at hij
    exact_mod_cast hij

theorem sampledCutoff_zero_left (x : ℕ) (hx : 10 ≤ x) (n : ℤ) (hn : n ≤ 1) :
    sampledCutoff x (by omega) n = 0 := by
  have hxR : (10 : ℝ) ≤ x := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hnR : (n : ℝ) ≤ 1 := by exact_mod_cast hn
  have ht : (n : ℝ) / x ≤ 1 / 10 := by
    apply (div_le_iff₀ hxpos).2
    linarith
  rw [sampledCutoff_apply, eta1_left _ (by linarith), max_eq_left (by linarith)]
  simp

theorem sampledCutoff_zero_right (x : ℕ) (hx : 0 < x) (n : ℤ) (hn : (x : ℤ) ≤ n) :
    sampledCutoff x hx n = 0 := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hnR : (x : ℝ) ≤ n := by exact_mod_cast hn
  rw [sampledCutoff_apply, eta1_zero_of_one_le _ ((le_div_iff₀ hxpos).2 (by linarith))]
  simp

theorem sampledCutoff_second_difference_support (x : ℕ) (hx : 10 ≤ x) :
    (TaoFiniteDifference.difference (TaoFiniteDifference.difference
      (sampledCutoff x (by omega)))).support ⊆
        (Finset.range x).image (fun n : ℕ => (n : ℤ) + 2) := by
  intro n hn
  rw [Finsupp.mem_support_iff] at hn
  have hlo : 2 ≤ n := by
    by_contra h
    apply hn
    rw [TaoFiniteDifference.second_difference_apply,
      sampledCutoff_zero_left x hx n (by omega),
      sampledCutoff_zero_left x hx (n - 1) (by omega),
      sampledCutoff_zero_left x hx (n - 2) (by omega)]
    ring
  have hhi : n < (x : ℤ) + 2 := by
    by_contra h
    apply hn
    rw [TaoFiniteDifference.second_difference_apply,
      sampledCutoff_zero_right x (by omega) n (by omega),
      sampledCutoff_zero_right x (by omega) (n - 1) (by omega),
      sampledCutoff_zero_right x (by omega) (n - 2) (by omega)]
    ring
  apply Finset.mem_image.mpr
  refine ⟨(n - 2).toNat, ?_, ?_⟩
  · simp only [Finset.mem_range]
    omega
  · omega

theorem sampledCutoff_second_difference_mass (x : ℕ) (hx : 10 ≤ x) :
    (∑ n ∈ (TaoFiniteDifference.difference (TaoFiniteDifference.difference
      (sampledCutoff x (by omega)))).support,
      ‖TaoFiniteDifference.difference (TaoFiniteDifference.difference
        (sampledCutoff x (by omega))) n‖) ≤ 40 / (x : ℝ) := by
  classical
  let d := TaoFiniteDifference.difference (TaoFiniteDifference.difference
    (sampledCutoff x (by omega)))
  change (∑ n ∈ d.support, ‖d n‖) ≤ _
  calc
    _ = ∑ n ∈ (Finset.range x).image (fun n : ℕ => (n : ℤ) + 2), ‖d n‖ := by
      apply Finset.sum_subset (sampledCutoff_second_difference_support x hx)
      intro n hn hnot
      rw [Finsupp.notMem_support_iff.mp hnot, norm_zero]
    _ = ∑ n ∈ Finset.range x, ‖d ((n : ℤ) + 2)‖ := by
      rw [Finset.sum_image]
      intro i hi j hj hij
      change (i : ℤ) + 2 = (j : ℤ) + 2 at hij
      omega
    _ = ∑ n ∈ Finset.range x,
        |eta1 (((n : ℝ) + 2) / x) - 2 * eta1 (((n : ℝ) + 1) / x) +
          eta1 ((n : ℝ) / x)| := by
      apply Finset.sum_congr rfl
      intro n hn
      dsimp [d]
      rw [TaoFiniteDifference.second_difference_apply]
      rw [show (n : ℤ) + 2 - 1 = (n : ℤ) + 1 by omega]
      simp only [sampledCutoff_apply]
      norm_num only [Int.cast_add, Int.cast_sub, Int.cast_ofNat, Int.cast_natCast,
        add_sub_cancel_right]
      exact norm_real_second_difference _ _ _
    _ ≤ _ := eta1_second_difference_mass x hx

theorem cutoff_fourier_decay (x : ℕ) (hx : 10 ≤ x) (α : AddCircle (1 : ℝ)) :
    ‖1 - fourier 1 α‖ ^ 2 *
      ‖TaoFourierIdentity.fourierPolynomial (Finset.range (x + 1))
        (fun n ↦ (eta1 ((n : ℝ) / x) : ℂ)) (fun n ↦ (n : ℤ)) α‖ ≤ 40 / (x : ℝ) := by
  have h := TaoFiniteDifference.second_difference_decay (sampledCutoff x (by omega)) α
  rw [sampledCutoff_transform] at h
  exact h.trans (sampledCutoff_second_difference_mass x hx)

end TaoFivePrimes

end

section

open MeasureTheory

namespace TaoFivePrimes

theorem norm_one_sub_fourier_coe (t : ℝ) :
    ‖1 - fourier 1 (t : AddCircle (1 : ℝ))‖ = 2 * |Real.sin (Real.pi * t)| := by
  have he : fourier 1 (t : AddCircle (1 : ℝ)) =
      Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    <;> ring
  rw [he, norm_sub_rev, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * t) / 2 = Real.pi * t by ring]
  simp [norm_mul, Real.norm_eq_abs]

theorem fourier_chord_lower_bound (t : ℝ) (ht : |t| ≤ 1 / 2) :
    4 * |t| ≤ ‖1 - fourier 1 (t : AddCircle (1 : ℝ))‖ := by
  have harg : |Real.pi * t| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hs := Real.mul_abs_le_abs_sin harg
  rw [abs_mul, abs_of_pos Real.pi_pos] at hs
  have hc : (2 / Real.pi) * (Real.pi * |t|) = 2 * |t| := by
    field_simp
  rw [hc] at hs
  rw [norm_one_sub_fourier_coe]
  linarith

theorem cutoff_fourier_real_decay (x : ℕ) (hx : 10 ≤ x) (t : ℝ)
    (ht : |t| ≤ 1 / 2) (ht0 : t ≠ 0) :
    ‖TaoFourierIdentity.fourierPolynomial (Finset.range (x + 1))
        (fun n ↦ (eta1 ((n : ℝ) / x) : ℂ)) (fun n ↦ (n : ℤ))
        (t : AddCircle (1 : ℝ))‖ ≤ 5 / (2 * (x : ℝ) * t ^ 2) := by
  let F := TaoFourierIdentity.fourierPolynomial (Finset.range (x + 1))
    (fun n ↦ (eta1 ((n : ℝ) / x) : ℂ)) (fun n ↦ (n : ℤ)) (t : AddCircle (1 : ℝ))
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have htpos : 0 < t ^ 2 := sq_pos_of_ne_zero ht0
  have h := cutoff_fourier_decay x hx (t : AddCircle (1 : ℝ))
  change ‖1 - fourier 1 (t : AddCircle (1 : ℝ))‖ ^ 2 * ‖F‖ ≤ 40 / (x : ℝ) at h
  have hs : (4 * |t|) ^ 2 ≤ ‖1 - fourier 1 (t : AddCircle (1 : ℝ))‖ ^ 2 := by
    gcongr
    exact fourier_chord_lower_bound t ht
  have hp := mul_le_mul_of_nonneg_right hs (norm_nonneg F)
  have hprod : 16 * t ^ 2 * ‖F‖ ≤ 40 / (x : ℝ) := by
    have heq : (4 * |t|) ^ 2 = 16 * t ^ 2 := by rw [mul_pow, sq_abs]; norm_num
    rw [heq] at hp
    exact hp.trans h
  have hscaled := (le_div_iff₀ hxpos).mp hprod
  change ‖F‖ ≤ _
  apply (le_div_iff₀ (show 0 < 2 * (x : ℝ) * t ^ 2 by positivity)).2
  nlinarith

theorem integral_inverse_square (r s : ℝ) (hr : 0 < r) (hrs : r ≤ s) :
    (∫ t in r..s, t ^ (-2 : ℤ)) = r⁻¹ - s⁻¹ := by
  rw [integral_zpow (Or.inr ⟨by norm_num, ?_⟩)]
  · norm_num
    ring
  · rw [Set.uIcc_of_le hrs]
    intro h
    exact (not_le_of_gt hr) h.1

theorem positive_tail_integral_bound (f : ℝ → ℝ) (hf : Continuous f)
    (B r : ℝ) (hB : 0 ≤ B) (hr : 0 < r) (hrhi : r ≤ 1 / 2)
    (hbound : ∀ t ∈ Set.Icc r (1 / 2), f t ≤ B * t ^ (-2 : ℤ)) :
    (∫ t in r..(1 / 2 : ℝ), f t) ≤ B / r := by
  have hzero : (0 : ℝ) ∉ Set.uIcc r (1 / 2) := by
    rw [Set.uIcc_of_le hrhi]
    intro h
    exact (not_le_of_gt hr) h.1
  have hg : IntervalIntegrable (fun t : ℝ => B * t ^ (-2 : ℤ)) volume r (1 / 2) :=
    (intervalIntegral.intervalIntegrable_zpow (Or.inr hzero)).const_mul B
  calc
    _ ≤ ∫ t in r..(1 / 2 : ℝ), B * t ^ (-2 : ℤ) :=
      intervalIntegral.integral_mono_on hrhi (hf.intervalIntegrable _ _) hg hbound
    _ = B * (r⁻¹ - 2) := by
      rw [intervalIntegral.integral_const_mul, integral_inverse_square r (1 / 2) hr hrhi]
      norm_num
    _ ≤ B / r := by rw [div_eq_mul_inv]; nlinarith

theorem negative_tail_integral_bound (f : ℝ → ℝ) (hf : Continuous f)
    (B r : ℝ) (hB : 0 ≤ B) (hr : 0 < r) (hrhi : r ≤ 1 / 2)
    (hbound : ∀ t ∈ Set.Icc (-(1 / 2 : ℝ)) (-r), f t ≤ B * t ^ (-2 : ℤ)) :
    (∫ t in (-(1 / 2 : ℝ))..(-r), f t) ≤ B / r := by
  have h := positive_tail_integral_bound (fun t => f (-t)) (hf.comp continuous_neg)
    B r hB hr hrhi (by
      intro t ht
      have hb := hbound (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
      simpa using hb)
  rw [intervalIntegral.integral_comp_neg] at h
  exact h

end TaoFivePrimes

end

section

open MeasureTheory

namespace TaoFivePrimes

theorem circle_tail_integral_bound (F : C(AddCircle (1 : ℝ), ℝ))
    (B r : ℝ) (hB : 0 ≤ B) (hr : 0 < r) (hrhi : r ≤ 1 / 2)
    (hbound : ∀ t : ℝ, 0 < |t| → |t| ≤ 1 / 2 →
      F (t : AddCircle (1 : ℝ)) ≤ B * t ^ (-2 : ℤ)) :
    (∫ α in {α : AddCircle (1 : ℝ) | r < ‖α‖}, F α
      ∂AddCircle.haarAddCircle) ≤ 2 * B / r := by
  classical
  let E : Set (AddCircle (1 : ℝ)) := {α | r < ‖α‖}
  let f : ℝ → ℝ := fun t => F (t : AddCircle (1 : ℝ))
  let A : Set ℝ := (fun t : ℝ => (t : AddCircle (1 : ℝ))) ⁻¹' E
  let g : ℝ → ℝ := A.indicator f
  have hE : MeasurableSet E := isOpen_lt continuous_const continuous_norm |>.measurableSet
  have hA : MeasurableSet A := hE.preimage (AddCircle.continuous_mk' (1 : ℝ)).measurable
  have hf : Continuous f := F.continuous.comp (AddCircle.continuous_mk' (1 : ℝ))
  have hg (a b : ℝ) : IntervalIntegrable g volume a b :=
    ⟨(hf.intervalIntegrable a b).1.indicator hA, (hf.intervalIntegrable a b).2.indicator hA⟩
  have hnorm (t : ℝ) (ht : |t| ≤ 1 / 2) : ‖(t : AddCircle (1 : ℝ))‖ = |t| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (by norm_num)).2 (by simpa using ht)
  have hcenter : (∫ t in (-r)..r, g t) = 0 := by
    calc
      _ = ∫ t in (-r)..r, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [Set.uIcc_of_le (by linarith)] at ht
        have htabs : |t| ≤ r := abs_le.mpr ⟨ht.1, ht.2⟩
        have hn : t ∉ A := by
          change ¬ r < ‖(t : AddCircle (1 : ℝ))‖
          rw [hnorm t (htabs.trans hrhi)]
          exact not_lt.mpr htabs
        exact Set.indicator_of_notMem hn f
      _ = 0 := by simp
  have hleft : (∫ t in (-(1 / 2 : ℝ))..(-r), g t) =
      ∫ t in (-(1 / 2 : ℝ))..(-r), f t := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
    intro t ht
    have htneg : t < 0 := by linarith [ht.2]
    have htabs : |t| ≤ 1 / 2 := by rw [abs_of_neg htneg]; linarith [ht.1]
    have hm : t ∈ A := by
      change r < ‖(t : AddCircle (1 : ℝ))‖
      rw [hnorm t htabs, abs_of_neg htneg]
      linarith [ht.2]
    exact Set.indicator_of_mem hm f
  have hright : (∫ t in r..(1 / 2 : ℝ), g t) =
      ∫ t in r..(1 / 2 : ℝ), f t := by
    apply intervalIntegral.integral_congr_Ioo_of_le hrhi
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    have htabs : |t| ≤ 1 / 2 := by rw [abs_of_pos htpos]; exact ht.2.le
    have hm : t ∈ A := by
      change r < ‖(t : AddCircle (1 : ℝ))‖
      rw [hnorm t htabs, abs_of_pos htpos]
      exact ht.1
    exact Set.indicator_of_mem hm f
  have hhaar : (∫ α in E, F α ∂AddCircle.haarAddCircle) =
      ∫ t in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), g t := by
    rw [← MeasureTheory.integral_indicator hE, AddCircle.integral_haarAddCircle]
    simp only [inv_one, one_smul]
    rw [← AddCircle.intervalIntegral_preimage (1 : ℝ) (-(1 / 2 : ℝ)) (E.indicator F)]
    norm_num only
    rfl
  have hp : (∫ t in r..(1 / 2 : ℝ), f t) ≤ B / r := by
    apply positive_tail_integral_bound f hf B r hB hr hrhi
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    exact hbound t (abs_pos.mpr htpos.ne') (by rw [abs_of_pos htpos]; exact ht.2)
  have hn : (∫ t in (-(1 / 2 : ℝ))..(-r), f t) ≤ B / r := by
    apply negative_tail_integral_bound f hf B r hB hr hrhi
    intro t ht
    have htneg : t < 0 := by linarith [ht.2]
    exact hbound t (abs_pos.mpr htneg.ne) (by rw [abs_of_neg htneg]; linarith [ht.1])
  change (∫ α in E, F α ∂AddCircle.haarAddCircle) ≤ _
  rw [hhaar, ← intervalIntegral.integral_add_adjacent_intervals
    (hg (-(1 / 2)) (-r)) (hg (-r) (1 / 2)),
    ← intervalIntegral.integral_add_adjacent_intervals (hg (-r) r) (hg r (1 / 2)),
    hleft, hcenter, hright]
  rw [mul_div_assoc]
  linarith

theorem cutoff_circle_tail_integral_bound (x : ℕ) (hx : 10 ≤ x)
    (r : ℝ) (hr : 0 < r) (hrhi : r ≤ 1 / 2) :
    (∫ α in {α : AddCircle (1 : ℝ) | r < ‖α‖},
      ‖TaoFourierIdentity.fourierPolynomial (Finset.range (x + 1))
        (fun n ↦ (eta1 ((n : ℝ) / x) : ℂ)) (fun n ↦ (n : ℤ)) α‖
        ∂AddCircle.haarAddCircle) ≤ 5 / ((x : ℝ) * r) := by
  let F : C(AddCircle (1 : ℝ), ℝ) :=
    ⟨fun α => ‖TaoFourierIdentity.fourierPolynomial (Finset.range (x + 1))
      (fun n ↦ (eta1 ((n : ℝ) / x) : ℂ)) (fun n ↦ (n : ℤ)) α‖,
      (TaoFourierIdentity.continuous_fourierPolynomial _ _ _).norm⟩
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have h := circle_tail_integral_bound F (5 / (2 * (x : ℝ))) r
    (by positivity) hr hrhi (by
      intro t ht ht'
      have hdec := cutoff_fourier_real_decay x hx t ht' (abs_pos.mp ht)
      have heq : 5 / (2 * (x : ℝ) * t ^ 2) = (5 / (2 * (x : ℝ))) * t ^ (-2 : ℤ) := by
        simp [zpow_neg, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
      change _ ≤ _
      rw [← heq]
      exact hdec)
  have heq : 2 * (5 / (2 * (x : ℝ))) / r = 5 / ((x : ℝ) * r) := by
    field_simp
  rw [heq] at h
  exact h

end TaoFivePrimes

end

section

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

end

section

open MeasureTheory
open scoped BigOperators ArithmeticFunction.vonMangoldt ComplexConjugate

namespace TaoFivePrimes

theorem complementary_correlation_of_psi (x : ℕ) (hx : (10 ^ 9 : ℝ) ≤ x)
    (hrhi : T0 / (3.6 * Real.pi * (x : ℝ)) ≤ 1 / 2)
    (ε : ℝ) (hε : |ε| ≤ 0.02)
    (hpsi : (∑ n ∈ Finset.range (x + 1), (Λ n : ℝ)) ≤ 6 * (x : ℝ)) :
    ‖∫ α in (majorArc x)ᶜ, S1 x α *
      conj (TaoFourierIdentity.fourierPolynomial (Finset.range (x + 1))
        (fun n ↦ (eta1 ((n : ℝ) / x) : ℂ)) (fun n ↦ (n : ℤ)) α)
        ∂AddCircle.haarAddCircle‖ ≤
      0.01 * ((2 / 3 : ℝ) * (1 + ε) * x) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hx10 : 10 ≤ x := by exact_mod_cast (show (10 : ℝ) ≤ x by linarith)
  let r : ℝ := T0 / (3.6 * Real.pi * (x : ℝ))
  have hr : 0 < r := by dsimp [r, T0]; positivity
  have hsize : 5000 ≤ T0 / (3.6 * Real.pi) := by
    apply (le_div_iff₀ (by positivity : 0 < 3.6 * Real.pi)).2
    unfold T0
    nlinarith [Real.pi_lt_four]
  have hxr : (x : ℝ) * r = T0 / (3.6 * Real.pi) := by
    dsimp [r]
    field_simp
  have hdiv : 5 / ((x : ℝ) * r) ≤ 1 / 1000 := by
    apply (div_le_iff₀ (mul_pos hxpos hr)).2
    rw [hxr]
    linarith
  have hE : (majorArc x)ᶜ = {α : AddCircle (1 : ℝ) | r < ‖α‖} := by
    ext α
    simp [majorArc, r]
  let f : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨S1 x, TaoFourierIdentity.continuous_fourierPolynomial _ _ _⟩
  let g : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨TaoFourierIdentity.fourierPolynomial (Finset.range (x + 1))
      (fun n ↦ (eta1 ((n : ℝ) / x) : ℂ)) (fun n ↦ (n : ℤ)),
      TaoFourierIdentity.continuous_fourierPolynomial _ _ _⟩
  have hL1 : (∫ α in (majorArc x)ᶜ, ‖g α‖ ∂AddCircle.haarAddCircle) ≤ 1 / 1000 := by
    have h := cutoff_circle_tail_integral_bound x hx10 r hr hrhi
    rw [← hE] at h
    exact h.trans hdiv
  have hcorr := norm_correlation_le_uniform f g (majorArc x)ᶜ
    (6 * (x : ℝ)) (by
      intro α
      exact (S1_norm_le_prime_mass x α).trans hpsi)
  change ‖∫ α in (majorArc x)ᶜ, f α * conj (g α) ∂AddCircle.haarAddCircle‖ ≤ _
  calc
    _ ≤ (6 * (x : ℝ)) * ∫ α in (majorArc x)ᶜ, ‖g α‖
        ∂AddCircle.haarAddCircle := hcorr
    _ ≤ (6 * (x : ℝ)) * (1 / 1000) :=
      mul_le_mul_of_nonneg_left hL1 (by positivity)
    _ ≤ _ := by
      have he := (abs_le.mp hε).1
      have hmul := mul_nonneg (show 0 ≤ (x : ℝ) from hxpos.le)
        (show 0 ≤ ε + 0.02 by linarith)
      nlinarith

end TaoFivePrimes

end

open MeasureTheory TaoFivePrimes
open scoped BigOperators ComplexConjugate
theorem solution (x : ℕ)
    (hr_lower : 1 / (2 * (x : ℝ)) ≤ T0 / (3.6 * Real.pi * (x : ℝ)))
    (hr_upper : T0 / (3.6 * Real.pi * (x : ℝ)) ≤ 1 / 2)
    (hc8 : (10 ^ 8 : ℝ) ≤ (1 / 10 : ℝ) * x)
    (hneat : (10 ^ 4 : ℝ) * (3 / 2 : ℝ) ≤ x)
    (halamo : 5 * (3 / 2 : ℝ) ≤ Real.log ((1 / 10 : ℝ) * x))
    (h10q : (10 ^ 8 : ℝ) * (9 / 4 : ℝ) ≤ x)
    (hr0b : 20 * 60 * Real.sqrt (3 / 2 : ℝ) ≤ T0 / (3.6 * Real.pi))
    (ε : ℝ) (hε : |ε| ≤ 0.02)
    (hmass : (∑ n ∈ Finset.range (x + 1),
      siftedVonMangoldt x n * eta1 ((n : ℝ) / x) ^ 2) =
        (2 / 3 : ℝ) * (1 + ε) * x) :
    ‖∫ α in (majorArc x)ᶜ, S1 x α *
      conj (TaoFourierIdentity.fourierPolynomial (Finset.range (x + 1))
        (fun n ↦ (eta1 ((n : ℝ) / x) : ℂ)) (fun n ↦ (n : ℤ)) α)
        ∂AddCircle.haarAddCircle‖ ≤
      0.01 * ((2 / 3 : ℝ) * (1 + ε) * x) := by
  apply TaoFivePrimes.complementary_correlation_of_psi x (by linarith) hr_upper ε hε
  exact TaoFivePrimes.prime_mass_le_six_mul x