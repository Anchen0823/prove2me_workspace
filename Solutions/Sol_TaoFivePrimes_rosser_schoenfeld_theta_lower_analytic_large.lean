import Theorems.Thm_TaoFivePrimes_schoenfeld_psi_error_large
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Reduction of `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_large`

Target (Rosser--Schoenfeld 1962, Theorem 4, eq. (3.14), large range):

    for every real t >= 10^10,   t * (1 - 1 / (2 log t)) < theta t.

This is the range beyond tabulated numerical verification. Nothing here is a
finite check: the range is handled by the explicit prime-counting input

    TaoFivePrimes.schoenfeld_psi_error_large :
        |psi y - y| <= y / (40 log y)          (y >= 10^8)

together with the elementary prime-power correction between the two Chebyshev
functions, Mathlib's

    Chebyshev.psi_sub_theta_le : psi y - theta y <= 2 sqrt y * log y.

Write `L = log t` and `t >= 10^10`. The two-sided input gives in particular the
**lower** half `psi t >= t - t/(40 L)`, so

    theta t >= psi t - 2 sqrt t * L >= t - t/(40 L) - 2 sqrt t * L.

Hence `theta t > t - t/(2 L) = t * (1 - 1/(2 L))` as soon as

    (19/40) * t / L > 2 * sqrt t * L,   i.e.   (19/40) * sqrt t > 2 * L^2.

On `t >= 10^10` that comparison is proved here from the elementary logarithmic
bound `log t <= 8 * t^(1/8)`, written with three nested square roots, and
`sqrt (sqrt t) >= 269.5` (which follows from `sqrt (10^5) >= 269.5`).

Only the **lower** half `psi t >= t - t/(40 log t)` of the two-sided input is
used; the excess half plays no role.

Nothing else is assumed: the file has no `sorry`, no `axiom`, and imports only
the platform node named above plus Mathlib.
-/

theorem solution (t : ℝ) (h1 : 10 ^ 10 ≤ t) :
    t * (1 - 1 / (2 * Real.log t)) < Chebyshev.theta t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hconv : t * (1 - 1 / (2 * Real.log t)) = t - t / (2 * Real.log t) := by
    have h2 : (2 : ℝ) * Real.log t ≠ 0 := by positivity
    field_simp
  -- the explicit two-sided Chebyshev input, at threshold 10^8 <= 10^10 <= t
  have hpsi := TaoFivePrimes.schoenfeld_psi_error_large t (by
    have h8 : ((10 : ℝ) ^ 8 : ℝ) ≤ (10 : ℝ) ^ 10 := by norm_num
    linarith)
  have hpsi_low : t - t / (40 * Real.log t) ≤ Chebyshev.psi t := by
    have hab := abs_le.mp hpsi
    linarith [hab.1]
  have hcorr : Chebyshev.psi t - Chebyshev.theta t ≤ 2 * Real.sqrt t * Real.log t :=
    Chebyshev.psi_sub_theta_le (by linarith)
  have htheta_low :
      t - t / (40 * Real.log t) - 2 * Real.sqrt t * Real.log t ≤ Chebyshev.theta t := by
    linarith
  -- numeric core: (19/40) * sqrt t > 2 * (log t)^2 on t >= 10^10
  have hs_t : (10 : ℝ) ^ 5 ≤ Real.sqrt t := by
    have h10 : ((10 : ℝ) ^ 5) ^ 2 ≤ t := by
      have : ((10 : ℝ) ^ 5) ^ 2 = (10 : ℝ) ^ 10 := by norm_num
      rw [this]
      exact h1
    exact Real.le_sqrt_of_sq_le h10
  have hss_t : (269.5 : ℝ) ≤ Real.sqrt (Real.sqrt t) := by
    have h := Real.sqrt_le_sqrt hs_t
    have h269 : (269.5 : ℝ) ≤ Real.sqrt ((10 : ℝ) ^ 5) := by
      refine Real.le_sqrt_of_sq_le ?_
      norm_num
    exact le_trans h269 h
  have hlog_bound : Real.log t ≤ 8 * Real.sqrt (Real.sqrt (Real.sqrt t)) := by
    have hs0 : 0 < Real.sqrt (Real.sqrt (Real.sqrt t)) := by positivity
    have ht_eq : t = Real.sqrt (Real.sqrt (Real.sqrt t)) ^ 8 := by
      have hh1 : Real.sqrt (Real.sqrt (Real.sqrt t)) ^ 2 = Real.sqrt (Real.sqrt t) :=
        Real.sq_sqrt (Real.sqrt_nonneg _)
      have hh2 : Real.sqrt (Real.sqrt t) ^ 2 = Real.sqrt t :=
        Real.sq_sqrt (Real.sqrt_nonneg _)
      have hh3 : Real.sqrt t ^ 2 = t := Real.sq_sqrt (le_of_lt ht0)
      calc t = ((Real.sqrt (Real.sqrt (Real.sqrt t)) ^ 2) ^ 2) ^ 2 := by rw [hh1, hh2, hh3]
        _ = Real.sqrt (Real.sqrt (Real.sqrt t)) ^ 8 := by ring
    have hlog_eq : Real.log t = 8 * Real.log (Real.sqrt (Real.sqrt (Real.sqrt t))) := by
      have h := congrArg Real.log ht_eq
      rw [Real.log_pow] at h
      exact h
    have hle := Real.log_le_sub_one_of_pos hs0
    linarith
  have hL2 : (Real.log t) ^ 2 ≤ 64 * Real.sqrt (Real.sqrt t) := by
    have hs2 : Real.sqrt (Real.sqrt (Real.sqrt t)) ^ 2 = Real.sqrt (Real.sqrt t) :=
      Real.sq_sqrt (Real.sqrt_nonneg _)
    have hnn : (0 : ℝ) ≤ Real.sqrt (Real.sqrt (Real.sqrt t)) := Real.sqrt_nonneg _
    have hlog_nn : (0 : ℝ) ≤ Real.log t := le_of_lt hlogt
    nlinarith [hlog_bound, hs2, hnn, hlog_nn]
  have hmain : 2 * (Real.log t) ^ 2 < (19 / 40) * Real.sqrt t := by
    have hs2 : Real.sqrt (Real.sqrt t) ^ 2 = Real.sqrt t := Real.sq_sqrt (Real.sqrt_nonneg _)
    have hpos : 0 < Real.sqrt (Real.sqrt t) := by positivity
    nlinarith [hL2, hs2, hpos, hss_t]
  have hm1 : 2 * Real.sqrt t * (Real.log t) ^ 2 < (19 / 40) * t := by
    have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
    have h := mul_lt_mul_of_pos_right hmain hs
    have hs2t : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt (le_of_lt ht0)
    nlinarith [h, hs2t]
  have hm2 : 2 * Real.sqrt t * Real.log t < (19 / 40) * (t / Real.log t) := by
    rw [← mul_div_assoc]
    rw [lt_div_iff₀ hlogt]
    nlinarith [hm1]
  have hsum : t / (2 * Real.log t) - t / (40 * Real.log t) =
      (19 / 40) * (t / Real.log t) := by
    have h2 : (2 : ℝ) * Real.log t ≠ 0 := by positivity
    have h40 : (40 : ℝ) * Real.log t ≠ 0 := by positivity
    field_simp
    ring
  rw [hconv]
  linarith
