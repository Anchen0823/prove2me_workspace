import Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_BlockFoundation
import Definitions.Def_TaoFivePrimes_Theorem51Sums
import Theorem51BlockPartition

set_option maxHeartbeats 800000

/-! # Type I block summation: the per-block envelope

Tao, arXiv:1201.6656v4, Section 5, the block step between (5.16) and
(5.17).  For a block of the form `2jq + q/2 < d ≤ 2(j+1)q + q/2` the
contribution to the Type I sum is bounded by

`Σ_{d in block, d odd} min ( x/(2jq + q/2) · log x + 4 (log 2) log 2x ,
                             4 (log 2) log 2x / |sin (2 π d α)| )`

Two facts produce this shape, and both are pure envelope algebra:

* **(freeze)** the first alternative `(1/2)(x/d) log x + 4 (log 2) log 2x`
  increases as `d` decreases, so on the block it is dominated by its value
  at the *left endpoint* `d = 2jq + q/2`;
* **(min)** the node's pointwise envelope is a `min` of the two
  alternatives, so it is dominated by either one; freezing only the
  `x/d` part while keeping the cosecant part is therefore legitimate.

The `4 (log 2) log 2x` term is carried through unchanged: it does not
depend on `d` and is the source of the per-block additive cost. -/

open Finset

namespace TaoFivePrimesBlock

/-! ## 8. Freezing the `x/d` term at the left endpoint -/

/-- **Freeze step.** If `d` is in block `j` (so `blockLeft q j < d`) and
`d > 0`, then the first alternative of the node's envelope at `d` is at
most its value at the left endpoint:

`(1/2)(x/d) log x + 4 (log 2) log 2x ≤ x / (2 (2jq + q/2)) · log x + 4 (log 2) log 2x`

(the factor `2` in the denominator is the node's `1/2`, rewritten as
`x / (2 · blockLeft)`).  Requires `0 < x` and `0 ≤ log x` to keep the
direction of the comparison. -/
lemma freeze_x_div {q d j : ℕ} {x : ℝ}
    (hx : 0 < x) (hlx : 0 ≤ Real.log x) (hq : 0 < q)
    (hleft : blockLeft q j < (d : ℝ)) (_hd : 0 < (d : ℝ)) :
    (1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x)
      ≤ x / (2 * blockLeft q j) * Real.log x + 4 * Real.log 2 * Real.log (2 * x) := by
  have hbl : 0 < blockLeft q j := blockLeft_pos hq j
  -- `x/d ≤ x/blockLeft` because `blockLeft ≤ d` and `x > 0`
  have hdvd : x / (d : ℝ) ≤ x / blockLeft q j := by
    exact div_le_div_of_nonneg_left hx.le hbl hleft.le
  have hstep : (1 / 2) * (x / (d : ℝ)) ≤ x / (2 * blockLeft q j) := by
    have h2 : (0 : ℝ) < 2 := by norm_num
    -- `x / (2 * bL) = (x / bL) / 2` and `(1/2) * (x/d) = (x/d)/2`
    have heq1 : x / (2 * blockLeft q j) = (x / blockLeft q j) / 2 := by
      rw [div_mul_eq_div_div, div_right_comm]
    have heq2 : (1 / 2) * (x / (d : ℝ)) = (x / (d : ℝ)) / 2 := by ring
    rw [heq1, heq2]
    exact div_le_div_of_nonneg_right hdvd h2.le
  have : (1 / 2) * (x / (d : ℝ)) * Real.log x
      ≤ x / (2 * blockLeft q j) * Real.log x :=
    mul_le_mul_of_nonneg_right hstep hlx
  linarith

/-- **Envelope domination.** Any `W` obeying the node's pointwise envelope
at `d` is bounded by either alternative.  This is the `min`-splitting used
to choose the second alternative on a block. -/
lemma envelope_le_second {x alpha : ℝ} {d : ℕ} {W : ℕ → ℝ}
    (hWb : W d ≤
      (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then
        (1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x)
      else min ((1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x))
        (4 * Real.log 2 * Real.log (2 * x) / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|))) :
    W d ≤
      (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then
        (1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x)
      else 4 * Real.log 2 * Real.log (2 * x) / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|) := by
  refine hWb.trans ?_
  by_cases h : Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    exact min_le_right _ _

/-- **Frozen envelope, vanishing sine.** When `sin (2πdα) = 0` the node's
envelope is exactly the first alternative, and the freeze step bounds it by
the block's frozen first alternative. -/
lemma envelope_frozen_vanish {q d j : ℕ} {x alpha : ℝ} {W : ℕ → ℝ}
    (hx : 0 < x) (hlx : 0 ≤ Real.log x) (hq : 0 < q)
    (hleft : blockLeft q j < (d : ℝ)) (hd : 0 < (d : ℝ))
    (hsin : Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0)
    (hWb : W d ≤
      (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then
        (1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x)
      else min ((1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x))
        (4 * Real.log 2 * Real.log (2 * x) / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|))) :
    W d ≤ x / (2 * blockLeft q j) * Real.log x + 4 * Real.log 2 * Real.log (2 * x) := by
  have h := hWb
  rw [if_pos hsin] at h
  exact h.trans (freeze_x_div hx hlx hq hleft hd)

/-- **Frozen envelope, nonvanishing sine.** When `sin (2πdα) ≠ 0` the node's
envelope is the `min` of the two alternatives, so it is dominated by the
block envelope: frozen first alternative in the first slot, the actual
cosecant term in the second. -/
lemma envelope_frozen_nonvanish {q d j : ℕ} {x alpha : ℝ} {W : ℕ → ℝ}
    (hx : 0 < x) (hlx : 0 ≤ Real.log x) (hq : 0 < q)
    (hleft : blockLeft q j < (d : ℝ)) (hd : 0 < (d : ℝ))
    (hsin : Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) ≠ 0)
    (hWb : W d ≤
      (if Real.sin (Real.pi * (2 * alpha) * (d : ℝ)) = 0 then
        (1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x)
      else min ((1 / 2) * (x / (d : ℝ)) * Real.log x + 4 * Real.log 2 * Real.log (2 * x))
        (4 * Real.log 2 * Real.log (2 * x) / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|))) :
    W d ≤
      min (x / (2 * blockLeft q j) * Real.log x + 4 * Real.log 2 * Real.log (2 * x))
        (4 * Real.log 2 * Real.log (2 * x) / |Real.sin (Real.pi * (2 * alpha) * (d : ℝ))|) := by
  have h := hWb
  rw [if_neg hsin] at h
  exact h.trans (le_min ((min_le_left _ _).trans (freeze_x_div hx hlx hq hleft hd))
    (min_le_right _ _))

end TaoFivePrimesBlock
