import examples.«five-primes».CutoffEnergy

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
