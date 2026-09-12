import Mathlib

import Definitions.Def_TaoFivePrimes_ArcSplit

import Theorems.Thm_TaoFivePrimes_schoenfeld_psi_error_large

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

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

/-- A weight vanishing below the sifting threshold loses only nonprime mass. -/
theorem weighted_sieve_loss_le (x : ℕ) (w : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n ∧ w n ≤ 1)
    (hzero : ∀ n, n ≤ Nat.sqrt x → w n = 0) :
    |(∑ n ∈ Finset.range (x + 1), siftedVonMangoldt x n * w n) -
      (∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) * w n)| ≤
      Chebyshev.psi x - Chebyshev.theta x := by
  have hp (n : ℕ) :
      0 ≤ ((Λ n : ℝ) - siftedVonMangoldt x n) * w n ∧
      ((Λ n : ℝ) - siftedVonMangoldt x n) * w n ≤
        if n.Prime then 0 else (Λ n : ℝ) := by
    unfold siftedVonMangoldt
    by_cases hc : n.Coprime (primorial (Nat.sqrt x))
    · simp only [if_pos hc, sub_self, zero_mul]
      constructor
      · exact le_rfl
      · split_ifs <;> positivity
    · simp only [if_neg hc, sub_zero]
      constructor
      · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hw n).1
      · by_cases hn : n.Prime
        · have hsmall : n ≤ Nat.sqrt x := by
            apply hn.dvd_primorial_iff.mp
            exact not_not.mp ((hn.coprime_iff_not_dvd).not.mp hc)
          simp [hn, hzero n hsmall]
        · simp only [hn, if_false]
          exact (mul_le_mul_of_nonneg_left (hw n).2
            ArithmeticFunction.vonMangoldt_nonneg).trans_eq (mul_one _)
  have hnonneg : 0 ≤ ∑ n ∈ Finset.range (x + 1),
      ((Λ n : ℝ) - siftedVonMangoldt x n) * w n :=
    Finset.sum_nonneg (fun n _ => (hp n).1)
  have heq : (∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) * w n) -
      (∑ n ∈ Finset.range (x + 1), siftedVonMangoldt x n * w n) =
      ∑ n ∈ Finset.range (x + 1), ((Λ n : ℝ) - siftedVonMangoldt x n) * w n := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [sub_mul]
  rw [abs_sub_comm, heq, abs_of_nonneg hnonneg]
  apply (Finset.sum_le_sum (fun n _ => (hp n).2)).trans_eq
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, Finset.sum_filter]
  have hs : Finset.range (x + 1) = insert 0 (Finset.Ioc 0 x) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [hs, Finset.sum_insert (by simp)]
  simp

end TaoFivePrimes

end

section

namespace TaoFivePrimes

theorem sieve_log_error_budget (x : ℝ) (hx : 10 ^ 9 ≤ x) :
    2 * Real.sqrt x * Real.log x ≤ x / 150 := by
  have hx0 : 0 ≤ x := by linarith
  have hs := Real.sq_sqrt hx0
  have hs0 := Real.sqrt_nonneg x
  have hslo : 30000 ≤ Real.sqrt x := by nlinarith
  have hl := Real.log_le_sub_one_of_pos
    (show 0 < Real.sqrt x / 10000 by positivity)
  rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt hx0] at hl
  have hlog : Real.log 10000 ≤ 36 := by
    have hten := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10)
    rw [show (10000 : ℝ) = 10 ^ 4 by norm_num, Real.log_pow]
    norm_num
    linarith
  have hb : Real.log x ≤ Real.sqrt x / 5000 + 70 := by linarith
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * Real.sqrt x by positivity)
  have ht := mul_nonneg hs0 (show 0 ≤ Real.sqrt x - 30000 by linarith)
  nlinarith

end TaoFivePrimes

end

section

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

theorem eta1_zero_below_sqrt (x : ℕ) (hx : 100 ≤ x) (n : ℕ)
    (hn : n ≤ Nat.sqrt x) : eta1 ((n : ℝ) / x) = 0 := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hs : 10 ≤ Nat.sqrt x := Nat.le_sqrt.mpr (by omega)
  have hsq := Nat.sqrt_le' x
  have hnx : 10 * n ≤ x := by nlinarith
  have hreal : 10 * (n : ℝ) ≤ x := by exact_mod_cast hnx
  have ht : (n : ℝ) / x ≤ 1 / 10 := (div_le_iff₀ hxpos).2 (by linarith)
  rw [eta1_left _ (by linarith)]
  exact max_eq_left (by linarith)

theorem quadratic_sieve_loss (x : ℕ) (hx : (10 ^ 9 : ℝ) ≤ x) :
    |(∑ n ∈ Finset.range (x + 1), siftedVonMangoldt x n * eta1 ((n : ℝ) / x) ^ 2) -
      (∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) * eta1 ((n : ℝ) / x) ^ 2)| ≤
      (x : ℝ) / 150 := by
  have hweight (n : ℕ) : 0 ≤ eta1 ((n : ℝ) / x) ^ 2 ∧
      eta1 ((n : ℝ) / x) ^ 2 ≤ 1 := by
    have h := eta1_bounds ((n : ℝ) / x)
    constructor
    · positivity
    · nlinarith
  have hzero (n : ℕ) (hn : n ≤ Nat.sqrt x) : eta1 ((n : ℝ) / x) ^ 2 = 0 := by
    rw [eta1_zero_below_sqrt x (by exact_mod_cast (show (100 : ℝ) ≤ x by linarith)) n hn]
    norm_num
  calc
    _ ≤ Chebyshev.psi x - Chebyshev.theta x := weighted_sieve_loss_le x _ hweight hzero
    _ ≤ 2 * Real.sqrt x * Real.log x :=
      (le_abs_self _).trans (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith))
    _ ≤ _ := sieve_log_error_budget (x : ℝ) hx

end TaoFivePrimes

end

section

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

/-- The explicit errors from Tao's Lemmas 4.1 and 4.3 fit the two-percent budget. -/
theorem quadratic_mass_error_budget (x L : ℝ) (hx : 10 ^ 9 ≤ x)
    (hL : 15 / 2 ≤ L) :
    x / (20 * L) + 2.52 * Real.sqrt x ≤ x / 75 := by
  have hx0 : 0 ≤ x := by linarith
  have hs := Real.sq_sqrt hx0
  have hs0 := Real.sqrt_nonneg x
  have hslo : 378 ≤ Real.sqrt x := by nlinarith
  have hfirst : x / (20 * L) ≤ x / 150 := by
    apply (div_le_iff₀ (by linarith : 0 < 20 * L)).2
    nlinarith [mul_nonneg hx0 (show 0 ≤ L - 15 / 2 by linarith)]
  have hsecond : 2.52 * Real.sqrt x ≤ x / 150 := by
    nlinarith [mul_nonneg hs0 (show 0 ≤ Real.sqrt x - 378 by linarith)]
  linarith

/-- Normalize a checked absolute mass error into the exact existential target. -/
theorem quadratic_mass_normalize (x M : ℝ) (hx : 0 < x)
    (hM : |M - (2 / 3) * x| ≤ x / 75) :
    ∃ ε : ℝ, |ε| ≤ 0.02 ∧ M = (2 / 3) * (1 + ε) * x := by
  refine ⟨(M - (2 / 3) * x) / ((2 / 3) * x), ?_, ?_⟩
  · rw [abs_div, abs_of_pos (by positivity : 0 < (2 / 3 : ℝ) * x)]
    apply (div_le_iff₀ (by positivity : 0 < (2 / 3 : ℝ) * x)).2
    linarith
  · field_simp
    <;> ring

/-- The quadratic mass target reduces to an unsifted estimate and the sieve loss. -/
theorem quadratic_prime_mass_of_estimates (x : ℕ)
    (hx : (10 ^ 9 : ℝ) ≤ x) (hlog : 15 / 2 ≤ Real.log ((x : ℝ) / 10))
    (hmain : |(∑ n ∈ Finset.range (x + 1),
        (Λ n : ℝ) * eta1 ((n : ℝ) / x) ^ 2) - (2 / 3 : ℝ) * x| ≤
        (x : ℝ) / (20 * Real.log ((x : ℝ) / 10)))
    (hsieve : |(∑ n ∈ Finset.range (x + 1),
        siftedVonMangoldt x n * eta1 ((n : ℝ) / x) ^ 2) -
        (∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) * eta1 ((n : ℝ) / x) ^ 2)| ≤
        2.52 * Real.sqrt x) :
    ∃ ε : ℝ, |ε| ≤ 0.02 ∧
      (∑ n ∈ Finset.range (x + 1),
        siftedVonMangoldt x n * eta1 ((n : ℝ) / x) ^ 2) =
        (2 / 3 : ℝ) * (1 + ε) * x := by
  apply quadratic_mass_normalize (x : ℝ) _ (by linarith)
  have h := abs_sub_le
    (∑ n ∈ Finset.range (x + 1), siftedVonMangoldt x n * eta1 ((n : ℝ) / x) ^ 2)
    (∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) * eta1 ((n : ℝ) / x) ^ 2)
    ((2 / 3 : ℝ) * x)
  have hb := quadratic_mass_error_budget (x : ℝ) (Real.log ((x : ℝ) / 10)) hx hlog
  linarith

/-- The sieve loss is proved; only the unsifted weighted estimate is assumed. -/
theorem quadratic_prime_mass_of_unsifted (x : ℕ)
    (hx : (10 ^ 9 : ℝ) ≤ x) (hlog : 15 / 2 ≤ Real.log ((x : ℝ) / 10))
    (hmain : |(∑ n ∈ Finset.range (x + 1),
        (Λ n : ℝ) * eta1 ((n : ℝ) / x) ^ 2) - (2 / 3 : ℝ) * x| ≤
        (x : ℝ) / (20 * Real.log ((x : ℝ) / 10))) :
    ∃ ε : ℝ, |ε| ≤ 0.02 ∧
      (∑ n ∈ Finset.range (x + 1),
        siftedVonMangoldt x n * eta1 ((n : ℝ) / x) ^ 2) =
        (2 / 3 : ℝ) * (1 + ε) * x := by
  apply quadratic_mass_normalize (x : ℝ) _ (by linarith)
  have h := abs_sub_le
    (∑ n ∈ Finset.range (x + 1), siftedVonMangoldt x n * eta1 ((n : ℝ) / x) ^ 2)
    (∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) * eta1 ((n : ℝ) / x) ^ 2)
    ((2 / 3 : ℝ) * x)
  have hs := quadratic_sieve_loss x hx
  have hb : (x : ℝ) / (20 * Real.log ((x : ℝ) / 10)) ≤ (x : ℝ) / 150 := by
    apply (div_le_iff₀ (by linarith : 0 < 20 * Real.log ((x : ℝ) / 10))).2
    nlinarith [mul_nonneg (show 0 ≤ (x : ℝ) by positivity)
      (show 0 ≤ Real.log ((x : ℝ) / 10) - 15 / 2 by linarith)]
  linarith

end TaoFivePrimes

end

section

open MeasureTheory
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

theorem quadratic_vonMangoldt_abel (a b A B : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (A * (n : ℝ) + B) ^ 2 * (Λ n : ℝ)) =
      (A * b + B) ^ 2 * Chebyshev.psi b -
      (A * a + B) ^ 2 * Chebyshev.psi a -
      ∫ t in Set.Ioc a b, (2 * (A * t + B) * A) * Chebyshev.psi t := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => (A * t + B) ^ 2)
      (2 * (A * t + B) * A) t := by
    convert! (((hasDerivAt_id t).const_mul A).add_const B).pow 2 using 1 <;> simp
  have hder : deriv (fun t : ℝ => (A * t + B) ^ 2) =
      fun t => 2 * (A * t + B) * A := funext (fun t => (hd t).deriv)
  have hi : IntegrableOn (deriv (fun t : ℝ => (A * t + B) ^ 2)) (Set.Icc a b) := by
    rw [hder]
    exact (by fun_prop : Continuous (fun t : ℝ => 2 * (A * t + B) * A)).integrableOn_Icc
  have h := sum_mul_eq_sub_sub_integral_mul (fun n => (Λ n : ℝ)) ha hab
    (fun t _ => (hd t).differentiableAt) hi
  simpa only [hder, ← Chebyshev.psi_eq_sum_Icc] using h

end TaoFivePrimes

end

section

open MeasureTheory
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

/-- Abel summation for the three polynomial pieces; all boundary terms cancel. -/
theorem trapezoid_piecewise_abel (x : ℝ) (hx : 0 < x) :
    (∑ n ∈ Finset.Ioc ⌊x / 10⌋₊ ⌊x / 5⌋₊,
      ((10 / x) * (n : ℝ) + (-1)) ^ 2 * (Λ n : ℝ)) +
    (∑ n ∈ Finset.Ioc ⌊x / 5⌋₊ ⌊4 * x / 5⌋₊, (Λ n : ℝ)) +
    (∑ n ∈ Finset.Ioc ⌊4 * x / 5⌋₊ ⌊9 * x / 10⌋₊,
      ((-10 / x) * (n : ℝ) + 9) ^ 2 * (Λ n : ℝ)) =
    -(∫ t in Set.Ioc (x / 10) (x / 5),
        (2 * ((10 / x) * t + (-1)) * (10 / x)) * Chebyshev.psi t) -
      ∫ t in Set.Ioc (4 * x / 5) (9 * x / 10),
        (2 * ((-10 / x) * t + 9) * (-10 / x)) * Chebyshev.psi t := by
  have h1 := quadratic_vonMangoldt_abel (x / 10) (x / 5) (10 / x) (-1)
    (by positivity) (by linarith)
  have h2 := quadratic_vonMangoldt_abel (x / 5) (4 * x / 5) 0 1
    (by positivity) (by linarith)
  have h3 := quadratic_vonMangoldt_abel (4 * x / 5) (9 * x / 10) (-10 / x) 9
    (by positivity) (by linarith)
  have e1 : (10 / x) * (x / 10) + (-1) = 0 := by field_simp; ring
  have e2 : (10 / x) * (x / 5) + (-1) = 1 := by field_simp; ring
  have e3 : (-10 / x) * (4 * x / 5) + 9 = 1 := by field_simp; ring
  have e4 : (-10 / x) * (9 * x / 10) + 9 = 0 := by field_simp; ring
  simp only [e1, e2, e3, e4, zero_pow (by norm_num : 2 ≠ 0), one_pow,
    zero_mul, one_mul, sub_zero, zero_sub] at h1 h3
  simp only [zero_mul, zero_add, one_pow, one_mul, mul_zero,
    integral_zero, sub_zero] at h2
  linarith

end TaoFivePrimes

end

section

namespace TaoFivePrimes

/-- The squared trapezoid as three disjoint, left-open/right-closed pieces. -/
theorem eta1_sq_three_pieces (t : ℝ) :
    eta1 t ^ 2 =
      (if 1 / 10 < t ∧ t ≤ 1 / 5 then (10 * t - 1) ^ 2 else 0) +
      (if 1 / 5 < t ∧ t ≤ 4 / 5 then 1 else 0) +
      (if 4 / 5 < t ∧ t ≤ 9 / 10 then (9 - 10 * t) ^ 2 else 0) := by
  by_cases h0 : t ≤ 1 / 10
  · rw [eta1_left t (by linarith), max_eq_left (by linarith)]
    split_ifs <;> simp_all <;> linarith
  by_cases h1 : t ≤ 1 / 5
  · rw [eta1_left t h1, max_eq_right (by linarith)]
    split_ifs <;> simp_all <;> linarith
  by_cases h2 : t ≤ 4 / 5
  · rw [eta1_middle t ⟨by linarith, h2⟩]
    split_ifs <;> simp_all <;> linarith
  by_cases h3 : t ≤ 9 / 10
  · rw [eta1_right t (by linarith), max_eq_right (by linarith)]
    split_ifs <;> simp_all <;> linarith
  · rw [eta1_right t (by linarith), max_eq_left (by linarith)]
    split_ifs <;> simp_all <;> linarith

end TaoFivePrimes

end

section

open scoped BigOperators

namespace TaoFivePrimes

theorem mem_floor_Ioc_iff (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ ↔ a < (n : ℝ) ∧ (n : ℝ) ≤ b := by
  rw [Finset.mem_Ioc, Nat.floor_lt ha, Nat.le_floor_iff hb]

theorem sum_range_indicator_Ioc (N a b : ℕ) (hb : b ≤ N) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.range (N + 1), if n ∈ Finset.Ioc a b then f n else 0) =
      ∑ n ∈ Finset.Ioc a b, f n := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    omega
  · intro n _
    rfl

end TaoFivePrimes

end

section

open MeasureTheory
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

theorem sampled_eta1_sq_partition (x : ℝ) (hx : 0 < x) (n : ℕ) :
    eta1 ((n : ℝ) / x) ^ 2 =
      (if n ∈ Finset.Ioc ⌊x / 10⌋₊ ⌊x / 5⌋₊ then
        ((10 / x) * (n : ℝ) + (-1)) ^ 2 else 0) +
      (if n ∈ Finset.Ioc ⌊x / 5⌋₊ ⌊4 * x / 5⌋₊ then 1 else 0) +
      (if n ∈ Finset.Ioc ⌊4 * x / 5⌋₊ ⌊9 * x / 10⌋₊ then
        ((-10 / x) * (n : ℝ) + 9) ^ 2 else 0) := by
  have h1 : n ∈ Finset.Ioc ⌊x / 10⌋₊ ⌊x / 5⌋₊ ↔
      1 / 10 < (n : ℝ) / x ∧ (n : ℝ) / x ≤ 1 / 5 := by
    rw [mem_floor_Ioc_iff _ _ (by positivity) (by positivity),
      lt_div_iff₀ hx, div_le_iff₀ hx]
    constructor <;> rintro ⟨ha, hb⟩ <;> constructor <;> linarith
  have h2 : n ∈ Finset.Ioc ⌊x / 5⌋₊ ⌊4 * x / 5⌋₊ ↔
      1 / 5 < (n : ℝ) / x ∧ (n : ℝ) / x ≤ 4 / 5 := by
    rw [mem_floor_Ioc_iff _ _ (by positivity) (by positivity),
      lt_div_iff₀ hx, div_le_iff₀ hx]
    constructor <;> rintro ⟨ha, hb⟩ <;> constructor <;> linarith
  have h3 : n ∈ Finset.Ioc ⌊4 * x / 5⌋₊ ⌊9 * x / 10⌋₊ ↔
      4 / 5 < (n : ℝ) / x ∧ (n : ℝ) / x ≤ 9 / 10 := by
    rw [mem_floor_Ioc_iff _ _ (by positivity) (by positivity),
      lt_div_iff₀ hx, div_le_iff₀ hx]
    constructor <;> rintro ⟨ha, hb⟩ <;> constructor <;> linarith
  have h := eta1_sq_three_pieces ((n : ℝ) / x)
  simp only [← h1, ← h2, ← h3] at h
  have e1 : 10 * ((n : ℝ) / x) - 1 = (10 / x) * (n : ℝ) + (-1) := by ring
  have e3 : 9 - 10 * ((n : ℝ) / x) = (-10 / x) * (n : ℝ) + 9 := by ring
  simpa only [e1, e3] using h

theorem unsifted_quadratic_mass_abel (x : ℕ) (hx : 0 < x) :
    (∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) * eta1 ((n : ℝ) / x) ^ 2) =
    -(∫ t in Set.Ioc ((x : ℝ) / 10) ((x : ℝ) / 5),
        (2 * ((10 / (x : ℝ)) * t + (-1)) * (10 / (x : ℝ))) * Chebyshev.psi t) -
      ∫ t in Set.Ioc (4 * (x : ℝ) / 5) (9 * (x : ℝ) / 10),
        (2 * ((-10 / (x : ℝ)) * t + 9) * (-10 / (x : ℝ))) * Chebyshev.psi t := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hb (t : ℝ) (ht : t ≤ x) : ⌊t⌋₊ ≤ x := by
    simpa using Nat.floor_le_floor ht
  rw [← trapezoid_piecewise_abel (x : ℝ) hxpos]
  rw [← sum_range_indicator_Ioc x _ _ (hb _ (by linarith)),
    ← sum_range_indicator_Ioc x _ _ (hb _ (by linarith)),
    ← sum_range_indicator_Ioc x _ _ (hb _ (by linarith))]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [sampled_eta1_sq_partition (x : ℝ) hxpos n]
  split_ifs <;> ring

end TaoFivePrimes

end

section

open MeasureTheory

namespace TaoFivePrimes

theorem quadratic_derivative_moment (a b A B : ℝ) (hab : a ≤ b) :
    (∫ t in Set.Ioc a b, (2 * (A * t + B) * A) * t) =
      (2 * A ^ 2 / 3) * (b ^ 3 - a ^ 3) + A * B * (b ^ 2 - a ^ 2) := by
  rw [← intervalIntegral.integral_of_le hab]
  have he : (fun t : ℝ => (2 * (A * t + B) * A) * t) =
      fun t => (2 * A ^ 2) * t ^ 2 + (2 * A * B) * t := by
    funext t
    ring
  rw [he, intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun t : ℝ => (2 * A ^ 2) * t ^ 2)).intervalIntegrable a b)
    ((by fun_prop : Continuous (fun t : ℝ => (2 * A * B) * t)).intervalIntegrable a b)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_pow, integral_id]
  norm_num
  ring

theorem trapezoid_main_term (x : ℝ) (hx : 0 < x) :
    -(∫ t in Set.Ioc (x / 10) (x / 5),
        (2 * ((10 / x) * t + (-1)) * (10 / x)) * t) -
      (∫ t in Set.Ioc (4 * x / 5) (9 * x / 10),
        (2 * ((-10 / x) * t + 9) * (-10 / x)) * t) = (2 / 3) * x := by
  rw [quadratic_derivative_moment _ _ _ _ (by linarith),
    quadratic_derivative_moment _ _ _ _ (by linarith)]
  field_simp
  ring

end TaoFivePrimes

end

section

open MeasureTheory

namespace TaoFivePrimes

theorem quadratic_derivative_integral (a b A B : ℝ) (hab : a ≤ b) :
    (∫ t in Set.Ioc a b, 2 * (A * t + B) * A) =
      (A * b + B) ^ 2 - (A * a + B) ^ 2 := by
  rw [← intervalIntegral.integral_of_le hab]
  have he : (fun t : ℝ => 2 * (A * t + B) * A) =
      fun t => (2 * A ^ 2) * t + (2 * A * B) := by funext t; ring
  rw [he, intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun t : ℝ => (2 * A ^ 2) * t)).intervalIntegrable a b)
    (continuous_const.intervalIntegrable a b)]
  rw [intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem trapezoid_kernel_integrals (x : ℝ) (hx : 0 < x) :
    (∫ t in Set.Ioc (x / 10) (x / 5), 2 * ((10 / x) * t + (-1)) * (10 / x)) = 1 ∧
    (∫ t in Set.Ioc (4 * x / 5) (9 * x / 10),
      -(2 * ((-10 / x) * t + 9) * (-10 / x))) = 1 := by
  constructor
  · rw [quadratic_derivative_integral _ _ _ _ (by linarith)]
    field_simp
    ring
  · rw [integral_neg, quadratic_derivative_integral _ _ _ _ (by linarith)]
    field_simp
    ring

end TaoFivePrimes

end

section

open MeasureTheory

namespace TaoFivePrimes

/-- Transfer a uniform Chebyshev error through a nonnegative continuous kernel. -/
theorem weighted_psi_error (a b δ : ℝ) (hab : a ≤ b) (g : ℝ → ℝ)
    (hg : Continuous g) (hg0 : ∀ t ∈ Set.Ioc a b, 0 ≤ g t)
    (hψ : ∀ t ∈ Set.Ioc a b, |Chebyshev.psi t - t| ≤ δ) :
    |∫ t in Set.Ioc a b, g t * (Chebyshev.psi t - t)| ≤
      δ * ∫ t in Set.Ioc a b, g t := by
  have hi : IntervalIntegrable (fun t : ℝ => Chebyshev.psi t - t) volume a b :=
    Chebyshev.psi_mono.intervalIntegrable.sub (continuous_id.intervalIntegrable a b)
  have hp : IntegrableOn (fun t => g t * (Chebyshev.psi t - t)) (Set.Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
      (hi.continuousOn_mul hg.continuousOn)
  have hq : IntegrableOn (fun t => δ * g t) (Set.Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
      ((continuous_const.mul hg).intervalIntegrable a b)
  calc
    _ ≤ ∫ t in Set.Ioc a b, |g t * (Chebyshev.psi t - t)| := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (fun t => g t * (Chebyshev.psi t - t))
          (μ := volume.restrict (Set.Ioc a b)))
    _ ≤ ∫ t in Set.Ioc a b, δ * g t := by
      apply setIntegral_mono_on hp.abs hq measurableSet_Ioc
      intro t ht
      rw [abs_mul, abs_of_nonneg (hg0 t ht)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hψ t ht) (hg0 t ht)
    _ = _ := integral_const_mul δ g

end TaoFivePrimes

end

section

open MeasureTheory
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

theorem weighted_psi_difference (a b δ : ℝ) (hab : a ≤ b) (g : ℝ → ℝ)
    (hg : Continuous g) (hg0 : ∀ t ∈ Set.Ioc a b, 0 ≤ g t)
    (hψ : ∀ t ∈ Set.Ioc a b, |Chebyshev.psi t - t| ≤ δ) :
    |(∫ t in Set.Ioc a b, g t * Chebyshev.psi t) -
      (∫ t in Set.Ioc a b, g t * t)| ≤ δ * ∫ t in Set.Ioc a b, g t := by
  have hp : IntegrableOn (fun t => g t * Chebyshev.psi t) (Set.Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
      (Chebyshev.psi_mono.intervalIntegrable.continuousOn_mul hg.continuousOn)
  have ht : IntegrableOn (fun t => g t * t) (Set.Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
      ((hg.mul continuous_id).intervalIntegrable a b)
  have h := weighted_psi_error a b δ hab g hg hg0 hψ
  simp only [mul_sub, integral_sub hp ht] at h
  exact h

theorem unsifted_mass_error_of_uniform (x : ℕ) (hx : 0 < x) (δ : ℝ)
    (hψ : ∀ t ∈ Set.Ioc ((x : ℝ) / 10) (9 * (x : ℝ) / 10),
      |Chebyshev.psi t - t| ≤ δ) :
    |(∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) * eta1 ((n : ℝ) / x) ^ 2) -
      (2 / 3 : ℝ) * x| ≤ 2 * δ := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  let u : ℝ → ℝ := fun t => 2 * ((10 / (x : ℝ)) * t + (-1)) * (10 / (x : ℝ))
  let d : ℝ → ℝ := fun t => -(2 * ((-10 / (x : ℝ)) * t + 9) * (-10 / (x : ℝ)))
  have hu0 : ∀ t ∈ Set.Ioc ((x : ℝ) / 10) ((x : ℝ) / 5), 0 ≤ u t := by
    intro t ht
    dsimp [u]
    have h : 1 < (10 / (x : ℝ)) * t := by
      rw [div_mul_eq_mul_div, lt_div_iff₀ hxpos]
      linarith [ht.1]
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)
  have hd0 : ∀ t ∈ Set.Ioc (4 * (x : ℝ) / 5) (9 * (x : ℝ) / 10), 0 ≤ d t := by
    intro t ht
    dsimp [d]
    have h : 0 ≤ (-10 / (x : ℝ)) * t + 9 := by
      have hh : (10 / (x : ℝ)) * t ≤ 9 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hxpos]
        linarith [ht.2]
      rw [neg_div, neg_mul]
      linarith
    apply neg_nonneg.mpr
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) h)
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) hxpos.le)
  have hu := weighted_psi_difference ((x : ℝ) / 10) ((x : ℝ) / 5) δ
    (by linarith) u (by dsimp [u]; fun_prop) hu0 (by
      intro t ht
      exact hψ t ⟨ht.1, by linarith [ht.2]⟩)
  have hd := weighted_psi_difference (4 * (x : ℝ) / 5) (9 * (x : ℝ) / 10) δ
    (by linarith) d (by dsimp [d]; fun_prop) hd0 (by
      intro t ht
      exact hψ t ⟨by linarith [ht.1], ht.2⟩)
  have hk := trapezoid_kernel_integrals (x : ℝ) hxpos
  change (∫ t in Set.Ioc ((x : ℝ) / 10) ((x : ℝ) / 5), u t) = 1 ∧
    (∫ t in Set.Ioc (4 * (x : ℝ) / 5) (9 * (x : ℝ) / 10), d t) = 1 at hk
  rw [hk.1, mul_one] at hu
  rw [hk.2, mul_one] at hd
  have hm := unsifted_quadratic_mass_abel x hx
  have hmain := trapezoid_main_term (x : ℝ) hxpos
  have hD (f : ℝ → ℝ) :
      (∫ t in Set.Ioc (4 * (x : ℝ) / 5) (9 * (x : ℝ) / 10), d t * f t) =
      -(∫ t in Set.Ioc (4 * (x : ℝ) / 5) (9 * (x : ℝ) / 10),
        (2 * ((-10 / (x : ℝ)) * t + 9) * (-10 / (x : ℝ))) * f t) := by
    simp only [d, neg_mul, integral_neg]
  rw [sub_eq_add_neg, ← hD Chebyshev.psi] at hm
  rw [sub_eq_add_neg, ← hD (fun t => t)] at hmain
  have hu' := abs_le.mp hu
  have hd' := abs_le.mp hd
  apply abs_le.mpr
  dsimp [u] at hu'
  constructor <;> linarith

end TaoFivePrimes

end

section

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

/-- Reduction to a two-sided explicit Chebyshev estimate above 10^8. -/
theorem quadratic_mass_of_chebyshev_error (x : ℕ)
    (hx : (10 ^ 9 : ℝ) ≤ x) (hlog : 15 / 2 ≤ Real.log ((x : ℝ) / 10))
    (hsource : ∀ y : ℝ, 10 ^ 8 ≤ y →
      |Chebyshev.psi y - y| ≤ y / (40 * Real.log y)) :
    ∃ ε : ℝ, |ε| ≤ 0.02 ∧
      (∑ n ∈ Finset.range (x + 1),
        siftedVonMangoldt x n * eta1 ((n : ℝ) / x) ^ 2) =
        (2 / 3 : ℝ) * (1 + ε) * x := by
  apply quadratic_prime_mass_of_unsifted x hx hlog
  have hxpos : 0 < x := by exact_mod_cast (show (0 : ℝ) < x by linarith)
  have huniform : ∀ t ∈ Set.Ioc ((x : ℝ) / 10) (9 * (x : ℝ) / 10),
      |Chebyshev.psi t - t| ≤ (x : ℝ) / (40 * Real.log ((x : ℝ) / 10)) := by
    intro t ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have hlogs : Real.log ((x : ℝ) / 10) ≤ Real.log t :=
      Real.log_le_log (by positivity) ht.1.le
    calc
      _ ≤ t / (40 * Real.log t) := hsource t (by linarith [ht.1])
      _ ≤ t / (40 * Real.log ((x : ℝ) / 10)) :=
        div_le_div_of_nonneg_left ht0 (by linarith) (by linarith)
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith [ht.2]) (by linarith)
  have h := unsifted_mass_error_of_uniform x hxpos
    ((x : ℝ) / (40 * Real.log ((x : ℝ) / 10))) huniform
  convert h using 1 <;> ring

end TaoFivePrimes

end

open scoped BigOperators
open TaoFivePrimes
theorem solution (x : ℕ)
    (hc8 : (10 ^ 8 : ℝ) ≤ (1 / 10 : ℝ) * x)
    (hneat : (10 ^ 4 : ℝ) * (3 / 2 : ℝ) ≤ x)
    (halamo : 5 * (3 / 2 : ℝ) ≤ Real.log ((1 / 10 : ℝ) * x))
    (h10q : (10 ^ 8 : ℝ) * (9 / 4 : ℝ) ≤ x) :
    ∃ ε : ℝ, |ε| ≤ 0.02 ∧
      (∑ n ∈ Finset.range (x + 1), siftedVonMangoldt x n * eta1 ((n : ℝ) / x) ^ 2) =
        (2 / 3 : ℝ) * (1 + ε) * x := by
  apply TaoFivePrimes.quadratic_mass_of_chebyshev_error x (by linarith)
  · have he : (x : ℝ) / 10 = (1 / 10 : ℝ) * x := by ring
    rw [he]
    linarith
  · exact TaoFivePrimes.schoenfeld_psi_error_large