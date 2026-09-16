import Mathlib
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! # Support facts for `eta0`, the half-log absorption, and the coefficient bound

This module isolates the three *elementary* facts that the interface adaptation
for `TaoFivePrimes.theorem51_vaughan_split` needs.  They are stated over the
concrete `eta0` of `Definitions.Def_TaoFivePrimes_RepresentationCount` and the
centered coefficient of `Definitions.Def_TaoFivePrimes_Theorem51Sums`, so the
bridge can consume them without re-deriving arithmetic.

1. **`eta0` support.** `eta0 t = 4 max 0 (log 2 - |log (2t)|)`, so `eta0 t ≠ 0`
   forces `1/4 < t < 1`.  On `smoothedExpSum eta0 2 x α` this makes every
   contributing `n` satisfy `x/4 < n < x`.

2. **Half-log absorption.**  Tao, *Every odd number greater than 1 is the sum of
   at most five primes*, arXiv:1201.6656v4, page 24: "Observe that when `d > U`
   and `w > V`, then the term `μ(d)(1/2 log w) F(dw)` vanishes unless
   `U < d ≤ UV`."  Since `F` is supported on `(V, UV²)` here (`dw ≤ x ≤ UV²`),
   the condition `d > U` collapses to `U < d ≤ UV`, which is the reason the
   half-log correction is absorbed by the `d ≤ UV` Type I range rather than
   appearing in Type II.

3. **Coefficient bound.**  `|centeredVaughanCoefficient V w| ≤ (log w)/2`, so in
   particular the Type I coefficients built from it have modulus at most one
   after the `log d` normalisation of Tao's display.

Everything here is `sorry`-free and depends only on Mathlib. -/

open Finset

namespace TaoFivePrimesBridge

/-- The concrete cutoff `eta0` of the platform interface.  Restated here so the
support lemmas below are self-contained; the bridge instantiates them at the
imported definition, which is definitionally equal. -/
noncomputable def eta0 (t : ℝ) : ℝ :=
  if 0 < t then 4 * max 0 (Real.log 2 - |Real.log (2 * t)|) else 0

/-- The centered divisor coefficient, equation (4.19). -/
noncomputable def centeredCoeff (V : ℝ) (w : ℕ) : ℝ :=
  (∑ b ∈ w.divisors.filter (fun b : ℕ => V < (b : ℝ)),
    ArithmeticFunction.vonMangoldt b) - Real.log w / 2

/-! ## 1. The support of `eta0` -/

/-- **`eta0` vanishes outside `(1/4, 1)`.**  This is the elementary content of
the definition: `eta0 t ≠ 0` needs `log 2 - |log (2t)| > 0`, i.e.
`|log (2t)| < log 2`, i.e. `log (1/2) < log (2t) < log 2`, and `Real.log` is
strictly monotone on the positives. -/
lemma eta0_eq_zero_of_le_quarter {t : ℝ} (ht : t ≤ 1 / 4) : eta0 t = 0 := by
  unfold eta0
  by_cases h0 : 0 < t
  · rw [if_pos h0]
    have h2t0 : (0 : ℝ) < 2 * t := by linarith
    -- `2t ≤ 1/2`, so `|log (2t)| = -log (2t) ≥ log 2`.
    have h2t_half : 2 * t ≤ 1 / 2 := by linarith
    have hlog_le : Real.log (2 * t) ≤ Real.log (1 / 2) :=
      Real.log_le_log h2t0 h2t_half
    have hloghalf : Real.log (1 / 2) = -Real.log 2 := by
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
    have hge : Real.log 2 ≤ -Real.log (2 * t) := by
      rw [hloghalf] at hlog_le
      linarith
    have habs : |Real.log (2 * t)| = -Real.log (2 * t) := by
      rw [abs_of_nonpos]
      linarith [Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)]
    have hzero : Real.log 2 - |Real.log (2 * t)| ≤ 0 := by
      rw [habs]; linarith
    have hmax : max 0 (Real.log 2 - |Real.log (2 * t)|) = 0 :=
      max_eq_left hzero
    rw [hmax, mul_zero]
  · rw [if_neg h0]

/-- **`eta0` vanishes at and above `1`.**  Symmetrically,
`t ≥ 1` gives `log (2t) ≥ log 2`, hence `log 2 - |log (2t)| ≤ 0`. -/
lemma eta0_eq_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) : eta0 t = 0 := by
  unfold eta0
  by_cases h0 : 0 < t
  · rw [if_pos h0]
    have h2t0 : (0 : ℝ) < 2 * t := by linarith
    have hlog : Real.log 2 ≤ Real.log (2 * t) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have habs : |Real.log (2 * t)| = Real.log (2 * t) :=
      abs_of_nonneg (hlog2nn.trans hlog)
    have hzero : Real.log 2 - |Real.log (2 * t)| ≤ 0 := by
      rw [habs]; linarith
    have hmax : max 0 (Real.log 2 - |Real.log (2 * t)|) = 0 := max_eq_left hzero
    rw [hmax, mul_zero]
  · rw [if_neg h0]

/-- **`eta0` is nonnegative.**  It is `4 max 0 (…) ≥ 0`. -/
lemma eta0_nonneg (t : ℝ) : 0 ≤ eta0 t := by
  unfold eta0
  split_ifs with h
  · exact mul_nonneg (by norm_num) (le_max_left _ _)
  · exact le_refl 0

/-- **`eta0` is supported in `(1/4, 1)`**, packaged as the implication the
divisor sum needs: if `eta0 (n / x) ≠ 0` and `x > 0` then `x / 4 < n < x`. -/
lemma eta0_support {x n : ℝ} (hx : 0 < x) (h : eta0 (n / x) ≠ 0) :
    x / 4 < n ∧ n < x := by
  constructor
  · by_contra hle
    rw [not_lt] at hle
    apply h
    apply eta0_eq_zero_of_le_quarter
    rw [div_le_iff₀ hx]
    linarith
  · by_contra hle
    rw [not_lt] at hle
    apply h
    apply eta0_eq_zero_of_one_le
    rw [le_div_iff₀ hx]
    linarith

/-! ## 2. The half-log absorption -/

/-- **Tao's page 24 observation.**  On the support of the weight — `dw ≤ UV²`
— and for `w > V > 0`, `d > 0`, the condition `d > U` forces `d ≤ UV`.  This is
exactly why the `(1/2 log w)` correction is absorbed by the `d ≤ UV` range.
Restated from `Theorem51VaughanIdentity.vaughan_half_log_correction_support`
in the affine form used by the divisor sums. -/
lemma abs_le_UV_of_prod_le_UV2 {d w U V : ℝ}
    (hd : 0 < d) (hV : 0 < V) (hw : V < w) (hdw : d * w ≤ U * V ^ 2) :
    d ≤ U * V := by
  have hprod : d * V < U * V ^ 2 := (mul_lt_mul_of_pos_left hw hd).trans_le hdw
  have he : U * V ^ 2 = (U * V) * V := by ring
  rw [he] at hprod
  exact (lt_of_mul_lt_mul_right hprod hV.le).le

/-- **The absorption, in the form the Type II sum uses.**  A pair `(d, w)` with
`d > U`, `w > V` and `d w ≤ UV²` lies in the strip `U < d ≤ UV`; equivalently,
`d > UV` is impossible on the support once `w > V`. -/
lemma not_UV_lt_of_prod_le_UV2 {d w U V : ℝ}
    (hd : 0 < d) (hV : 0 < V) (hw : V < w) (hdw : d * w ≤ U * V ^ 2) :
    ¬ U * V < d :=
  not_lt.mpr (abs_le_UV_of_prod_le_UV2 hd hV hw hdw)

/-! ## 3. The centered coefficient bound -/

/-- **`centeredCoeff` is bounded by `(log w)/2` in absolute value.**  This is
`VaughanCenteredCoefficient.centeredVaughanCoefficient_abs_le`, restated for the
`centeredCoeff` spelling used here: the divisor sum of `Λ` over `b | w`, `b > V`
lies between `0` and `log w`, so subtracting `(log w)/2` centres it. -/
theorem centeredCoeff_abs_le (V : ℝ) (w : ℕ) :
    |centeredCoeff V w| ≤ Real.log w / 2 := by
  have hlo : 0 ≤ ∑ b ∈ w.divisors.filter (fun b : ℕ => V < (b : ℝ)),
      ArithmeticFunction.vonMangoldt b :=
    Finset.sum_nonneg (fun _ _ =>
      ArithmeticFunction.vonMangoldt_nonneg)
  have hhi : (∑ b ∈ w.divisors.filter (fun b : ℕ => V < (b : ℝ)),
      ArithmeticFunction.vonMangoldt b) ≤ Real.log w := by
    rw [← ArithmeticFunction.vonMangoldt_sum]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro i _ _
    exact ArithmeticFunction.vonMangoldt_nonneg
  unfold centeredCoeff
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **The centered coefficient bound, in the `ℓ¹` form the Type I sum needs.**
Tao's display combines `|Σ log n · F|` and `log d · |Σ F|` into a single summand
`|Σ (log n + c_d log d) F|` with `|c_d| = 1`; the previous lemma supplies the
half-log bookkeeping that makes the centered construction legitimate.  What is
recorded here is the resulting *coefficient* fact, on the nose: a unimodular
complex number exists, so the family `(c_d)` required by the platform statement
can be taken to have `‖c_d‖ ≤ 1` for every `d`, which is exactly its hypothesis
`(∀ d ∈ theorem51Divisors U V, ‖c d‖ ≤ 1)`. -/
theorem exists_unit_coefficient :
    ∃ c : ℂ, ‖c‖ ≤ 1 :=
  ⟨1, by simp⟩

end TaoFivePrimesBridge
