import Mathlib

set_option autoImplicit false

private lemma cube_exp_neg_antitone_from (x : ℝ) (hx : 58 / 5 ≤ x) :
    x ^ 3 * Real.exp (-x) ≤ (58 / 5 : ℝ) ^ 3 * Real.exp (-(58 / 5 : ℝ)) := by
  let u : ℝ := x - 58 / 5
  have hu : 0 ≤ u := by
    dsimp [u]
    linarith
  have hseries := Real.sum_le_exp_of_nonneg (x := u) hu 4
  have hpoly : x ^ 3 ≤ (58 / 5 : ℝ) ^ 3 * Real.exp u := by
    rw [show x = 58 / 5 + u by dsimp [u]; ring]
    calc
      (58 / 5 + u) ^ 3 ≤ (58 / 5 : ℝ) ^ 3 *
          (∑ i ∈ Finset.range 4, u ^ i / (i.factorial : ℝ)) := by
        norm_num [Finset.sum_range_succ]
        nlinarith [mul_nonneg hu hu, mul_nonneg (mul_nonneg hu hu) hu]
      _ ≤ (58 / 5 : ℝ) ^ 3 * Real.exp u := by
        gcongr
  calc
    x ^ 3 * Real.exp (-x) ≤ ((58 / 5 : ℝ) ^ 3 * Real.exp u) * Real.exp (-x) := by
      gcongr
    _ = (58 / 5 : ℝ) ^ 3 * Real.exp (-(58 / 5 : ℝ)) := by
      calc
        (58 / 5 : ℝ) ^ 3 * Real.exp u * Real.exp (-x)
            = (58 / 5 : ℝ) ^ 3 * (Real.exp u * Real.exp (-x)) := by ring
        _ = (58 / 5 : ℝ) ^ 3 * Real.exp (-(58 / 5 : ℝ)) := by
          rw [← Real.exp_add]
          congr 1
          simp [u]
          ring

private lemma exp_neg_fifty_eight_fifths_lt :
    Real.exp (-(58 / 5 : ℝ)) < 1 / 105000 := by
  have h := Real.sum_le_exp_of_nonneg (x := (58 / 5 : ℝ)) (by norm_num) 20
  have hlarge : (105000 : ℝ) < Real.exp (58 / 5 : ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    exact lt_of_lt_of_le (by norm_num) h
  rw [Real.exp_neg]
  simpa [one_div] using one_div_lt_one_div_of_lt (by norm_num) hlarge

/-- The explicit numerical tail in Rosser--Schoenfeld (1975), Theorem 2, is below `0.025`
once `t ≥ 1300`.  This is only the numerical estimate, independent of any prime theorem. -/
theorem sondow_schoenfeld_tail_numeric (t : ℝ) (ht : 1300 ≤ t) :
    let R : ℝ := 9.645908801
    let X : ℝ := Real.sqrt (t / R)
    0.257634 * (1 + 0.96642 / X) * X ^ (3 / 4 : ℝ) * Real.exp (-X) * t < 0.025 := by
  dsimp
  let R : ℝ := 9.645908801
  let X : ℝ := Real.sqrt (t / R)
  have hR : 0 < R := by
    dsimp [R]
    norm_num
  have ht0 : 0 ≤ t := by linarith
  have hdiv0 : 0 ≤ t / R := div_nonneg ht0 hR.le
  have hX0 : 0 ≤ X := by
    dsimp [X]
    exact Real.sqrt_nonneg _
  have hsq : X ^ 2 = t / R := by
    dsimp [X]
    simpa using Real.sq_sqrt hdiv0
  have hX : 58 / 5 ≤ X := by
    have hdiv : (58 / 5 : ℝ) ^ 2 ≤ t / R := by
      apply (le_div_iff₀ hR).2
      nlinarith
    nlinarith
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have htX : t = R * X ^ 2 := by
    calc
      t = (t / R) * R := (div_mul_cancel₀ t hR.ne').symm
      _ = X ^ 2 * R := by rw [← hsq]
      _ = R * X ^ 2 := by ring
  have hfac : 1 + 0.96642 / X ≤ (1.084 : ℝ) := by
    calc
      1 + 0.96642 / X ≤ 1 + (0.084 : ℝ) := by
        gcongr
        apply (div_le_iff₀ hXpos).2
        nlinarith
      _ = 1.084 := by norm_num
  have hquarter : X ^ (-(1 / 4 : ℝ)) ≤ (3 / 5 : ℝ) := by
    have hbase : X ^ (-(1 / 4 : ℝ)) ≤ (58 / 5 : ℝ) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hX (by norm_num)
    refine hbase.trans ?_
    apply (Real.rpow_le_rpow_iff
      (x := (58 / 5 : ℝ) ^ (-(1 / 4 : ℝ))) (y := (3 / 5 : ℝ)) (z := (4 : ℝ))
      (by positivity) (by norm_num) (by norm_num)).mp
    rw [← Real.rpow_mul (by positivity)]
    norm_num [Real.rpow_neg, ← Real.rpow_natCast]
  have hrpow : X ^ (3 / 4 : ℝ) ≤ (3 / 5 : ℝ) * X := by
    rw [show (3 / 4 : ℝ) = 1 + -(1 / 4 : ℝ) by norm_num,
      Real.rpow_add hXpos, Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_right hquarter hX0]
  calc
    0.257634 * (1 + 0.96642 / X) * X ^ (3 / 4 : ℝ) * Real.exp (-X) * t
        = (0.257634 * (1 + 0.96642 / X) * X ^ (3 / 4 : ℝ) *
          Real.exp (-X) * R) * X ^ 2 := by rw [htX]; ring
    _ ≤ (0.257634 * 1.084 * ((3 / 5 : ℝ) * X) * Real.exp (-X) * R) * X ^ 2 := by
      gcongr
    _ = (0.257634 * 1.084 * (3 / 5 : ℝ) * R) * (X ^ 3 * Real.exp (-X)) := by ring
    _ ≤ (0.257634 * 1.084 * (3 / 5 : ℝ) * R) *
          ((58 / 5 : ℝ) ^ 3 * Real.exp (-(58 / 5 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left (cube_exp_neg_antitone_from X hX) (by positivity)
    _ < 0.025 := by
      have hpos : 0 < 0.257634 * 1.084 * (3 / 5 : ℝ) * R := by positivity
      calc
        (0.257634 * 1.084 * (3 / 5 : ℝ) * R) *
            ((58 / 5 : ℝ) ^ 3 * Real.exp (-(58 / 5 : ℝ)))
            < (0.257634 * 1.084 * (3 / 5 : ℝ) * R) *
              ((58 / 5 : ℝ) ^ 3 * (1 / 105000 : ℝ)) := by
                apply mul_lt_mul_of_pos_left _ hpos
                apply mul_lt_mul_of_pos_left exp_neg_fifty_eight_fifths_lt (by positivity)
        _ < 0.025 := by
          dsimp [R]
          norm_num
