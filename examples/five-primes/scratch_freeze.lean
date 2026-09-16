import Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_BlockFoundation
import Definitions.Def_TaoFivePrimes_Theorem51Sums

set_option maxHeartbeats 800000

/-! # §10 scratch: freezing inside the min -/

open Finset

namespace TaoFivePrimesScratch

/-- **Monotonicity of `min` in the first argument.** -/
lemma min_fst_mono {a a' b : ℝ} (h : a ≤ a') : min a b ≤ min a' b := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    exact le_min h le_rfl
  · rw [min_eq_right hba]
    exact le_min (le_trans hba h) le_rfl

/-- **The frozen envelope dominates the varying one on a block.**  For
`d ≥ L` with `0 < x`, `0 < L`, the first alternative at `L` dominates the one
at `d`. -/
lemma frozen_alt_le (x L d : ℝ) (hx : 0 ≤ x) (hL : 0 < L) (hd : L ≤ d)
    (hlogx : 0 ≤ Real.log x) :
    (1 / 2) * (x / d) * Real.log x ≤ (1 / 2) * (x / L) * Real.log x := by
  have hd0 : (0 : ℝ) < d := lt_of_lt_of_le hL hd
  have hdiv : x / d ≤ x / L := div_le_div_of_nonneg_left hx hL hd
  nlinarith

/-- **Freezing the first alternative inside the `min` loses nothing.** -/
lemma block_term_le_frozen (x L d C B : ℝ)
    (hx : 0 ≤ x) (hL : 0 < L) (hd : L ≤ d) (hlogx : 0 ≤ Real.log x) :
    min ((1 / 2) * (x / d) * Real.log x + C) B
      ≤ min ((1 / 2) * (x / L) * Real.log x + C) B := by
  apply min_fst_mono
  linarith [frozen_alt_le x L d hx hL hd hlogx]

/-- **Sum form.**  Freezing each term of a block at the left endpoint. -/
lemma block_sum_le_frozen {ι : Type*} (s : Finset ι) (x L C : ℝ) (B : ι → ℝ)
    (f : ι → ℝ) (hx : 0 ≤ x) (hL : 0 < L) (hlogx : 0 ≤ Real.log x)
    (hd : ∀ i ∈ s, L ≤ f i)
    (hterm : ∀ i ∈ s, min ((1 / 2) * (x / f i) * Real.log x + C) (B i)
      ≤ min ((1 / 2) * (x / L) * Real.log x + C) (B i)) :
    ∑ i ∈ s, min ((1 / 2) * (x / f i) * Real.log x + C) (B i)
      ≤ ∑ i ∈ s, min ((1 / 2) * (x / L) * Real.log x + C) (B i) :=
  Finset.sum_le_sum hterm

end TaoFivePrimesScratch
