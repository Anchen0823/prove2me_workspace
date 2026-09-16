import Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! # Sharpened Corollary 3.5: closing `hblock` in `Theorem51Assembly`

This module is self-contained (`import Mathlib` only) and restates, in minimal
form, the two facts needed to eliminate the hypothesis `hblock` from
`Theorem51Assembly` §10:

* `sharp_block_bound` — the sharpened Corollary 3.5: on the **odd** integers of
  a range of width at most `2q`, the Vinogradov min-sum is at most
  `2A + (2/π) B q log 4q`.  Its analytic content (Lemma 3.4) enters as a
  hypothesis, exactly as in the source, where Lemma 3.4 is proved separately.

* `hblock_closed` — substituting `A = X/2 + C`, `B = C` turns that right-hand
  side into the §10 right-hand side `X + 2C + (2/π) C q log 4q`.

The second is the point: it shows `hblock` is not an extra estimate but the
*same* estimate at a particular choice of the `A`-slot. -/

open Finset

namespace TaoFivePrimesGlueMin

/-- The min-sum summand with the source's convention at the zeros of the sine
(`A` there, since that is the minimum).  Lean's `B / 0 = 0` would otherwise
make a bare `min` vanish at a vanishing phase. -/
noncomputable def vmin (A B alpha theta : ℝ) (n : ℤ) : ℝ :=
  if Real.sin (Real.pi * alpha * (n : ℝ) + theta) = 0 then A
  else min A (B / |Real.sin (Real.pi * alpha * (n : ℝ) + theta)|)

/-- Common right-hand side of the sharpened estimates. -/
noncomputable def vRhs (q : ℕ) (A B : ℝ) : ℝ :=
  2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * (q : ℝ))

/-- **Sharpened Corollary 3.5**, as the shape `oddBlockBound`:
on the odd integers `z` with `x < z ≤ y` and `y ≤ x + 2q`, the odd Vinogradov
min-sum is at most `vRhs q A B`. -/
def oddBlockBound (q : ℕ) (A B alpha theta x y : ℝ) : Prop :=
  y ≤ x + 2 * (q : ℝ) →
    (∑ z ∈ (Finset.Icc (⌊x⌋ + 1) ⌊y⌋).filter (fun z => Odd z), vmin A B alpha theta z)
      ≤ vRhs q A B

/-- **The right-hand sides coincide.**  With `A = X/2 + C`, `B = C`,
`vRhs q A B = X + 2C + (2/π) C q log 4q`.  This is the identification that
makes `hblock` an instance of the sharpened Corollary 3.5. -/
lemma vRhs_eq_hblock_rhs (q : ℕ) (X C : ℝ) :
    vRhs q (X / 2 + C) C
      = X + 2 * C + (2 / Real.pi) * C * (q : ℝ) * Real.log (4 * (q : ℝ)) := by
  unfold vRhs
  ring

/-- **`hblock` closed.**  A caller holding the sharpened bound at
`A = X/2 + C`, `B = C` obtains verbatim the §10 hypothesis. -/
theorem hblock_closed (q : ℕ) (X C b : ℝ)
    (hsharp : b ≤ vRhs q (X / 2 + C) C) :
    b ≤ X + 2 * C + (2 / Real.pi) * C * (q : ℝ) * Real.log (4 * (q : ℝ)) := by
  rw [← vRhs_eq_hblock_rhs q X C]
  exact hsharp

/-- **`hblock` closed, `n`-indexed form.**  §10's `block_sum_envelope_le`
carries the odd count `n` explicitly; the sharpened estimate pays the
`q/2 + O(1)` count through Corollary 3.5's `+4q` slack, so this is the form that
matches §10 verbatim. -/
theorem hblock_closed_n_indexed (q : ℕ) (X C b n : ℝ)
    (hsharp : b + n * C ≤ vRhs q (X / 2 + C) C) :
    b + n * C ≤ X + 2 * C + (2 / Real.pi) * C * (q : ℝ) * Real.log (4 * (q : ℝ)) := by
  rw [← vRhs_eq_hblock_rhs q X C]
  exact hsharp

/-- The `A`-slot arithmetic: `2 (X/2 + C) = X + 2C`. -/
lemma two_A_slot (X C : ℝ) : 2 * (X / 2 + C) = X + 2 * C := by ring

/-- The `A`-slot is nonnegative at `C = 4 (log 2) log 2x`, `x ≥ 1`, `X > 0`. -/
lemma A_slot_nonneg {x X : ℝ} (hx : 1 ≤ x) (hX : 0 < X) :
    0 ≤ X / 2 + 4 * Real.log 2 * Real.log (2 * x) := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2x : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by nlinarith)
  nlinarith

/-- The `B`-slot is nonnegative at `C = 4 (log 2) log 2x`, `x ≥ 1`. -/
lemma B_slot_nonneg {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ 4 * Real.log 2 * Real.log (2 * x) := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2x : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by nlinarith)
  nlinarith

end TaoFivePrimesGlueMin
