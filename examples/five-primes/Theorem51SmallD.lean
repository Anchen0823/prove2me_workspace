import Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_BlockFoundation

set_option maxHeartbeats 800000

/-! # Type I block summation: the cosecant bound from (2.1) and (5.15)

Tao, arXiv:1201.6656v4, Section 5, the first half of (5.15).

**The chain.**  Let `4 α = a/q + β` with `|β| ≤ q^{-2}`, let `q ≥ 2` and
`q ⊥ a`, and let `2 d ≤ q`.  Then:

* `rdist_d_alpha_ge` gives `‖4 d α‖_{ℝ/ℤ} ≥ 1/(2q)`;
* inequality (2.1), lower half, turns this into `|sin (4 π d α)| ≥ 1/q`;
* hence `1 / |sin (4 π d α)| ≤ q`.

The last step needs `rdist (4 d α) > 0`, which follows from the lower bound
combined with `q > 0`; it is *not* automatic, and this is why the lemma is
stated with `0 < q` as an explicit hypothesis rather than derived. -/

open Finset

namespace TaoFivePrimesBlock

/-! ## 6. From (2.1)'s lower half to a cosecant bound -/

/-- **(2.1) + an explicit positive lower bound on `rdist`.**  If
`1/(2 r) ≤ rdist t` and `r > 0`, then `|sin (π t)| ≥ 1/r`; equivalently
`1 / |sin (π t)| ≤ r`.

The hypothesis `hr : 0 < r` is essential: it is what makes `rdist t`
strictly positive, and without it the reciprocal bound is false (take
`rdist t = 0`). -/
lemma inv_abs_sin_le_of_rdist_ge (t r : ℝ) (hr : 0 < r)
    (h : 1 / (2 * r) ≤ rdist t) :
    1 / |Real.sin (Real.pi * t)| ≤ r := by
  have hpos : 0 < rdist t := lt_of_lt_of_le (by positivity) h
  have hsin : 1 / r ≤ |Real.sin (Real.pi * t)| := by
    have h2 := two_rdist_le_abs_sin t
    have h3 : 2 * (1 / (2 * r)) ≤ 2 * rdist t :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    have h4 : 1 / r = 2 * (1 / (2 * r)) := by field_simp
    calc 1 / r = 2 * (1 / (2 * r)) := h4
      _ ≤ 2 * rdist t := h3
      _ ≤ |Real.sin (Real.pi * t)| := h2
  have hfinal := one_div_le_one_div_of_le (one_div_pos.mpr hr) hsin
  rwa [one_div_one_div] at hfinal

end TaoFivePrimesBlock
