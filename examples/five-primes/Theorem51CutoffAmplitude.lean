import Definitions.Def_TaoFivePrimes_RepresentationCount
import Mathlib.Tactic

namespace TaoFivePrimes

lemma eta0_zero_below_quarter {t : ℝ} (ht : t ≤ 1 / 4) : eta0 t = 0 := by
  unfold eta0
  split_ifs with hp
  · have hlog : Real.log (2 * t) ≤ -Real.log 2 := by
      have h := Real.log_le_log (show 0 < 2 * t by positivity)
        (show 2 * t ≤ (1 / 2 : ℝ) by linarith)
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv] at h
      exact h
    have hab : Real.log 2 ≤ |Real.log (2 * t)| := by
      linarith [neg_le_abs (Real.log (2 * t))]
    rw [max_eq_left (by linarith), mul_zero]
  · rfl

lemma eta0_zero_above_one {t : ℝ} (ht : 1 ≤ t) : eta0 t = 0 := by
  unfold eta0
  rw [if_pos (by linarith)]
  have hl : Real.log 2 ≤ Real.log (2 * t) := Real.log_le_log (by norm_num) (by linarith)
  have hm : Real.log 2 - |Real.log (2 * t)| ≤ 0 := by
    linarith [le_abs_self (Real.log (2 * t))]
  rw [max_eq_left hm, mul_zero]

lemma eta0_lower_piece {t : ℝ} (hlo : 1 / 4 ≤ t) (hhi : t ≤ 1 / 2) :
    eta0 t = 4 * Real.log (4 * t) := by
  have ht : 0 < t := by linarith
  have hneg : Real.log (2 * t) ≤ 0 := Real.log_nonpos (by positivity) (by linarith)
  have he : Real.log 2 + Real.log (2 * t) = Real.log (4 * t) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]
    congr 1
    ring
  unfold eta0
  rw [if_pos ht, abs_of_nonpos hneg, sub_neg_eq_add, he,
    max_eq_right (Real.log_nonneg (by linarith))]

lemma eta0_upper_piece {t : ℝ} (hlo : 1 / 2 ≤ t) (hhi : t ≤ 1) :
    eta0 t = -4 * Real.log t := by
  have ht : 0 < t := by linarith
  have hpos : 0 ≤ Real.log (2 * t) := Real.log_nonneg (by linarith)
  have he : Real.log 2 - Real.log (2 * t) = -Real.log t := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ht.ne']
    ring
  unfold eta0
  rw [if_pos ht, abs_of_nonneg hpos, he,
    max_eq_right (neg_nonneg.mpr (Real.log_nonpos ht.le hhi))]
  ring

/-- Actual odd-lattice amplitude in a Type I inner sum. -/
noncomputable def typeIOddAmplitude (x d : ℝ) (c : ℂ) (n : ℤ) : ℂ :=
  ((Real.log ((2 * n + 1 : ℤ) : ℝ) : ℂ) + c * (Real.log d : ℂ)) *
    (eta0 (d * ((2 * n + 1 : ℤ) : ℝ) / x) : ℂ)

lemma typeIOddAmplitude_finite (x d : ℝ) (c : ℂ) (hx : 0 < x) (hd : 0 < d) :
    Function.HasFiniteSupport (typeIOddAmplitude x d c) := by
  apply (Set.finite_Icc (0 : ℤ) ⌈x / d⌉).subset
  intro n hn
  by_contra hnot
  have hz : typeIOddAmplitude x d c n = 0 := by
    unfold typeIOddAmplitude
    suffices he : eta0 (d * ((2 * n + 1 : ℤ) : ℝ) / x) = 0 by rw [he]; simp
    simp only [Set.mem_Icc, not_and_or, not_le] at hnot
    rcases hnot with hlo | hhi
    · apply eta0_zero_below_quarter
      have hn0 : n ≤ -1 := by omega
      have hy : ((2 * n + 1 : ℤ) : ℝ) ≤ 0 := by exact_mod_cast (show 2 * n + 1 ≤ 0 by omega)
      have hh : d * ((2 * n + 1 : ℤ) : ℝ) / x ≤ 0 := div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hd.le hy) hx.le
      linarith
    · apply eta0_zero_above_one
      have hceil : x / d ≤ (⌈x / d⌉ : ℤ) := Int.le_ceil _
      have hnR : ((⌈x / d⌉ : ℤ) : ℝ) < n := by exact_mod_cast hhi
      have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (div_pos hx hd) (hceil.trans hnR.le)
      have hy : x / d ≤ ((2 * n + 1 : ℤ) : ℝ) := by push_cast; linarith
      apply (le_div_iff₀ hx).2
      have hh := (div_le_iff₀ hd).mp hy
      nlinarith
  exact hn hz

end TaoFivePrimes
