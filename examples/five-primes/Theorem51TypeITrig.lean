import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import examples.«five-primes».Theorem51PhaseAudit
import examples.«five-primes».Theorem51OddHarmonic

namespace TaoFivePrimes

/-- A global quadratic cosecant envelope on the positive half-quadrant. -/
lemma sine_quadratic_envelope (t : ℝ) (ht : 0 < t) (htpi : t ≤ Real.pi / 2) :
    t ^ 2 ≤ (1 + t ^ 2) * Real.sin t ^ 2 := by
  have htB : t ≤ (5 / 3 : ℝ) := by linarith [Real.pi_lt_d2]
  have ht3 : t ^ 2 ≤ 3 := by
    have hb := (sq_le_sq₀ ht.le (by norm_num : (0 : ℝ) ≤ 5 / 3)).2 htB
    norm_num at hb
    linarith
  let r : ℝ := 1 - t ^ 2 / 6
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hs : t * r ≤ Real.sin t := by
    have h := Real.sin_ge_sub_cube ht.le
    dsimp [r]
    nlinarith
  have hsin : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_pos])
  have hR : 1 ≤ (1 + t ^ 2) * r ^ 2 := by
    apply sub_nonneg.mp
    have he : (1 + t ^ 2) * r ^ 2 - 1 = t ^ 2 * (3 - t ^ 2) * (8 - t ^ 2) / 36 := by
      dsimp [r]
      ring
    rw [he]
    have h3 : 0 ≤ 3 - t ^ 2 := by linarith
    have h8 : 0 ≤ 8 - t ^ 2 := by linarith
    positivity
  calc
    t ^ 2 ≤ t ^ 2 * ((1 + t ^ 2) * r ^ 2) := by nlinarith [sq_nonneg t]
    _ = (1 + t ^ 2) * (t * r) ^ 2 := by ring
    _ ≤ (1 + t ^ 2) * Real.sin t ^ 2 :=
      mul_le_mul_of_nonneg_left ((sq_le_sq₀ (mul_nonneg ht.le hr) hsin.le).2 hs) (by positivity)

lemma cosecant_sq_le_inv_sq_add_one (t : ℝ) (ht : 0 < t) (htpi : t ≤ Real.pi / 2) :
    1 / Real.sin t ^ 2 ≤ 1 / t ^ 2 + 1 := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_pos])
  have h := sine_quadratic_envelope t ht htpi
  apply (div_le_iff₀ (sq_pos_of_pos hs)).2
  rw [show (1 / t ^ 2 + 1) * Real.sin t ^ 2 =
    ((1 + t ^ 2) * Real.sin t ^ 2) / t ^ 2 by field_simp]
  apply (le_div_iff₀ (sq_pos_of_pos ht)).2
  nlinarith

/-- Transfer the quadratic sine envelope to a weighted reciprocal. -/
lemma weighted_cosecant_envelope (d q t y : ℝ) (hd : 0 < d) (ht : 0 < t)
    (htpi : t ≤ Real.pi / 2) (hy : Real.sin t ≤ y)
    (hscale : d ^ 2 ≤ 0.41 * q ^ 2 * t ^ 2) :
    d / y ^ 2 ≤ 0.41 * q ^ 2 / d + d := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht (by linarith [Real.pi_pos])
  calc
    _ ≤ d / Real.sin t ^ 2 := div_le_div_of_nonneg_left hd.le
      (sq_pos_of_pos hs) ((sq_le_sq₀ hs.le (hs.le.trans hy)).2 hy)
    _ = d * (1 / Real.sin t ^ 2) := by ring
    _ ≤ d * (1 / t ^ 2 + 1) :=
      mul_le_mul_of_nonneg_left (cosecant_sq_le_inv_sq_add_one t ht htpi) hd.le
    _ = d / t ^ 2 + d := by ring
    _ ≤ _ := by
      suffices h : d / t ^ 2 ≤ 0.41 * q ^ 2 / d by linarith
      apply (div_le_div_iff₀ (sq_pos_of_pos ht) hd).2
      nlinarith

/-- A pointwise bound using the corrected phase endpoint, with numerical
slack that will be recovered by retaining odd summation indices. -/
lemma unit_cosecant_pointwise (alpha beta q d : ℝ) (hq : 1602 ≤ q)
    (hd : 0 < d) (hdq : d ≤ q - 1)
    (hphase : 4 * alpha = 1 / q + beta) (hbeta : |beta| ≤ 1 / q ^ 2) :
    d / Real.sin (2 * Real.pi * d * alpha) ^ 2 ≤ 0.41 * q ^ 2 / d + d := by
  have hq0 : 0 < q := by linarith
  have hqm : 0 < q - 1 := by linarith
  let t : ℝ := Real.pi * d * (q - 1) / (2 * q ^ 2)
  have ht : 0 < t := by dsimp [t]; positivity
  have hdqm : d * (q - 1) ≤ q ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hdq hqm.le
    nlinarith
  have htpi : t ≤ Real.pi / 2 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_left hdqm Real.pi_pos.le]
  have hbase : (25 / 8 : ℝ) * q ≤ Real.pi * (q - 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr Real.pi_gt_d2.le) hqm.le]
  have hscaled : (25 / 16 : ℝ) * d ≤ t * q := by
    have he : t * q = Real.pi * d * (q - 1) / (2 * q) := by
      dsimp [t]
      field_simp
    rw [he]
    apply (le_div_iff₀ (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_right hbase hd.le]
  have hscale : d ^ 2 ≤ 0.41 * q ^ 2 * t ^ 2 := by
    have hsq := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ (25 / 16 : ℝ) * d)
      (by positivity : 0 ≤ t * q)).2 hscaled
    nlinarith [sq_nonneg d]
  have hsin : Real.sin t ≤ Real.sin (2 * Real.pi * d * alpha) := by
    convert unit_phase_sine_lower alpha beta q d (by linarith) hd.le hdq hphase hbeta using 1
    congr 1
    dsimp [t]
    ring
  exact weighted_cosecant_envelope d q t _ hd ht htpi hsin hscale

lemma log_denominator_lower (q : ℕ) (hq : 1602 ≤ q) : (6.5 : ℝ) ≤ Real.log q := by
  have hqR : (1024 : ℝ) ≤ q := by exact_mod_cast (show 1024 ≤ q by omega)
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1024) hqR
  have he : Real.log (1024 : ℝ) = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
    norm_num
  rw [he] at h
  linarith [Real.log_two_gt_d9]

lemma typeI_numeric_slack (q : ℕ) (hq : 1602 ≤ q) :
    (q : ℝ) ^ 2 * (0.41 * (1.5 + 0.5 * Real.log q) + 1) ≤
      (4 / Real.pi ^ 2) * (q : ℝ) ^ 2 * Real.log (4 * Real.exp 1 * q / Real.pi) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlog := log_denominator_lower q hq
  have hpi : Real.pi ^ 2 ≤ 10 := by
    have h := (sq_le_sq₀ Real.pi_pos.le (by norm_num : (0 : ℝ) ≤ 3.15)).2 Real.pi_lt_d2.le
    norm_num at h
    linarith
  have hc : (0.4 : ℝ) ≤ 4 / Real.pi ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos Real.pi_pos)).2
    nlinarith
  have harg : Real.exp 1 * q ≤ 4 * Real.exp 1 * q / Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).2
    nlinarith [mul_le_mul_of_nonneg_left Real.pi_lt_four.le
      (show 0 ≤ Real.exp 1 * q by positivity)]
  have hl := Real.log_le_log (show 0 < Real.exp 1 * q by positivity) harg
  rw [Real.log_mul (Real.exp_ne_zero _) hq0.ne', Real.log_exp] at hl
  have hL : 0 ≤ 1 + Real.log q := by linarith
  calc
    _ ≤ (q : ℝ) ^ 2 * (0.4 * (1 + Real.log q)) := by gcongr; linarith
    _ = 0.4 * (q : ℝ) ^ 2 * (1 + Real.log q) := by ring
    _ ≤ _ := by gcongr

/-- The complete odd-index trigonometric sum bound with the constant needed
for (5.7), using the corrected lower phase endpoint. -/
theorem unit_typeI_trigonometric_sum (alpha beta : ℝ) (q : ℕ) (s : Finset ℕ)
    (hq : 1602 ≤ q)
    (hs : ∀ d ∈ s, 0 < d ∧ (d : ℝ) ≤ (q : ℝ) - 1 ∧ Odd d)
    (hphase : 4 * alpha = 1 / (q : ℝ) + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    (∑ d ∈ s, (d : ℝ) / Real.sin (2 * Real.pi * d * alpha) ^ 2) ≤
      (4 / Real.pi ^ 2) * (q : ℝ) ^ 2 * Real.log (4 * Real.exp 1 * q / Real.pi) := by
  have hslt : ∀ d ∈ s, d < q := by
    intro d hd
    have hb := (hs d hd).2.1
    exact_mod_cast (show (d : ℝ) < q by linarith)
  have hrec := odd_reciprocal_sum_le q s (fun d hd => ⟨(hslt d hd).le, (hs d hd).2.2⟩)
  have hsum := sum_indices_le_square q s hslt
  calc
    _ ≤ ∑ d ∈ s, (0.41 * (q : ℝ) ^ 2 / (d : ℝ) + d) := by
      apply Finset.sum_le_sum
      intro d hd
      exact unit_cosecant_pointwise alpha beta q d (by exact_mod_cast hq)
        (by exact_mod_cast (hs d hd).1) (hs d hd).2.1 hphase hbeta
    _ = 0.41 * (q : ℝ) ^ 2 * (∑ d ∈ s, 1 / (d : ℝ)) + ∑ d ∈ s, (d : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ 0.41 * (q : ℝ) ^ 2 * (1.5 + 0.5 * Real.log q) + (q : ℝ) ^ 2 := by gcongr
    _ = (q : ℝ) ^ 2 * (0.41 * (1.5 + 0.5 * Real.log q) + 1) := by ring
    _ ≤ _ := typeI_numeric_slack q hq

/-- Both signs of the unit numerator give the same squared sine sum. -/
theorem unit_typeI_trigonometric_sum_signed (alpha beta : ℝ) (a : ℤ)
    (q : ℕ) (s : Finset ℕ) (hq : 1602 ≤ q) (ha : a.natAbs = 1)
    (hs : ∀ d ∈ s, 0 < d ∧ (d : ℝ) ≤ (q : ℝ) - 1 ∧ Odd d)
    (hphase : 4 * alpha = (a : ℝ) / (q : ℝ) + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2) :
    (∑ d ∈ s, (d : ℝ) / Real.sin (2 * Real.pi * d * alpha) ^ 2) ≤
      (4 / Real.pi ^ 2) * (q : ℝ) ^ 2 * Real.log (4 * Real.exp 1 * q / Real.pi) := by
  rcases Int.natAbs_eq_iff.mp ha with ha | ha
  · norm_num at ha
    subst a
    exact unit_typeI_trigonometric_sum alpha beta q s hq hs (by simpa using hphase) hbeta
  · norm_num at ha
    subst a
    have hp : 4 * (-alpha) = 1 / (q : ℝ) + (-beta) := by
      norm_num at hphase
      rw [neg_div] at hphase
      linarith
    have h := unit_typeI_trigonometric_sum (-alpha) (-beta) q s hq hs hp (by simpa using hbeta)
    simpa only [mul_neg, Real.sin_neg, neg_sq] using h

lemma unit_regime_denominator_large (U V : ℝ) (q : ℕ)
    (hU : 40 ≤ U) (hV : 40 ≤ V) (hUVq : U * V < (q : ℝ) - 1) : 1602 ≤ q := by
  have h : (1601 : ℝ) < q := by
    nlinarith [mul_nonneg (show 0 ≤ U - 40 by linarith) (show 0 ≤ V - 40 by linarith)]
  have hn : 1601 < q := by exact_mod_cast h
  omega

/-- The full Type I outer-sum assembly. Its pointwise decay hypothesis is
the remaining smoothing obligation and is stated explicitly. -/
theorem unit_typeI_of_pointwise_decay (x alpha beta U V : ℝ) (a : ℤ) (q : ℕ)
    (s : Finset ℕ) (T : ℕ → ℂ)
    (hx : 1 ≤ x) (hU : 40 ≤ U) (hV : 40 ≤ V)
    (hUVq : U * V < (q : ℝ) - 1) (ha : a.natAbs = 1)
    (hs : ∀ d ∈ s, 0 < d ∧ (d : ℝ) ≤ U * V ∧ d.Coprime 2)
    (hphase : 4 * alpha = (a : ℝ) / q + beta)
    (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hdecay : ∀ d ∈ s, ‖T d‖ ≤ (24 * Real.log (4 * x) / x) *
      ((d : ℝ) / Real.sin (2 * Real.pi * d * alpha) ^ 2)) :
    (∑ d ∈ s, ‖T d‖) ≤ (96 / Real.pi ^ 2) * (x / (x / q) ^ 2) *
      Real.log (4 * x) * Real.log (4 * Real.exp 1 * q / Real.pi) := by
  have hq := unit_regime_denominator_large U V q hU hV hUVq
  have hx0 : 0 < x := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hlog : 0 ≤ Real.log (4 * x) := Real.log_nonneg (by linarith)
  have hK : 0 ≤ 24 * Real.log (4 * x) / x := by positivity
  have htrig := unit_typeI_trigonometric_sum_signed alpha beta a q s hq ha
    (fun d hd => ⟨(hs d hd).1, (hs d hd).2.1.trans hUVq.le,
      Nat.coprime_two_right.mp (hs d hd).2.2⟩) hphase hbeta
  calc
    _ ≤ ∑ d ∈ s, (24 * Real.log (4 * x) / x) *
        ((d : ℝ) / Real.sin (2 * Real.pi * d * alpha) ^ 2) :=
      Finset.sum_le_sum hdecay
    _ = (24 * Real.log (4 * x) / x) *
        (∑ d ∈ s, (d : ℝ) / Real.sin (2 * Real.pi * d * alpha) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ (24 * Real.log (4 * x) / x) *
        ((4 / Real.pi ^ 2) * (q : ℝ) ^ 2 * Real.log (4 * Real.exp 1 * q / Real.pi)) :=
      mul_le_mul_of_nonneg_left htrig hK
    _ = _ := by field_simp; ring

end TaoFivePrimes
