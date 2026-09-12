import Definitions.Def_TaoFivePrimes_RepresentationCount
import Mathlib

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
