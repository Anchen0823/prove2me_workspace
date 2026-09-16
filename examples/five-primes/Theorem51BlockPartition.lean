import Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

set_option maxHeartbeats 800000

/-! # Type I block summation: block structure

Companion to `Theorem51BlockFoundation`.  This module develops the
combinatorial half of Tao, arXiv:1201.6656v4, Section 5, (5.14) → (5.17):

* the initial segment `d ≤ q/2` and the blocks
  `2jq + q/2 < d ≤ 2(j+1)q + q/2`;
* the pointwise replacement inside a block by the *left endpoint*
  `2jq + q/2`, which is what makes the `log x` term summable;
* the reduction of the block's cosecant mass to the odd min-sum of
  Corollary 3.5.

All endpoint arithmetic is stated in the *doubled* integer form
(`4jq + q < 2d ≤ 4(j+1)q + q`), because `linarith` in this environment
treats `q/2` as an opaque atom and cannot relate it to `q`.  Halving is
performed once, by `div_lt_iff₀` / `le_div_iff₀`, after a `ring`
normalization that makes the two sides literally equal; every real
statement is then discharged from its integer shadow. -/

open Finset

namespace TaoFivePrimesBlock

/-! ## 6. The block index and its endpoints -/

/-- The left endpoint `2jq + q/2` of block `j`. -/
noncomputable def blockLeft (q : ℕ) (j : ℕ) : ℝ :=
  2 * (j : ℝ) * (q : ℝ) + (q : ℝ) / 2

/-- The right endpoint `2(j+1)q + q/2` of block `j`. -/
noncomputable def blockRight (q : ℕ) (j : ℕ) : ℝ :=
  2 * ((j : ℝ) + 1) * (q : ℝ) + (q : ℝ) / 2

lemma blockRight_eq (q j : ℕ) : blockRight q j = blockLeft q (j + 1) := by
  unfold blockRight blockLeft
  push_cast
  ring

lemma blockRight_sub_blockLeft (q j : ℕ) : blockRight q j - blockLeft q j = 2 * (q : ℝ) := by
  unfold blockRight blockLeft
  ring

/-- `blockLeft` is strictly increasing in the block index when `q > 0`. -/
lemma blockLeft_lt_succ {q : ℕ} (hq : 0 < q) (j : ℕ) :
    blockLeft q j < blockLeft q (j + 1) := by
  unfold blockLeft
  push_cast
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  linarith

/-- Every block left endpoint is positive. -/
lemma blockLeft_pos {q : ℕ} (hq : 0 < q) (j : ℕ) : 0 < blockLeft q j := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  unfold blockLeft
  have key : 2 * (j : ℝ) * (q : ℝ) + (q : ℝ) / 2
      = ((4 * (j : ℝ) * (q : ℝ)) + (q : ℝ)) / 2 := by ring
  rw [key]
  apply div_pos _ (by norm_num : (0 : ℝ) < 2)
  nlinarith

/-! ## 7. Membership in a block

The integer predicate `4jq + q < 2d ≤ 4(j+1)q + q` is the doubled form of
`blockLeft q j < d ≤ blockRight q j`. -/

/-- **Lower endpoint.** `4jq + q < 2d` halves to `blockLeft q j < d`. -/
lemma blockLeft_lt_of (q d j : ℕ) (h : 4 * j * q + q < 2 * d) :
    blockLeft q j < (d : ℝ) := by
  have hcast : ((4 * j * q + q : ℕ) : ℝ) < ((2 * d : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hcast
  unfold blockLeft
  have key : 2 * (j : ℝ) * (q : ℝ) + (q : ℝ) / 2
      = ((4 * (j : ℝ) * (q : ℝ)) + (q : ℝ)) / 2 := by ring
  rw [key, div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- **Upper endpoint.** `2d ≤ 4(j+1)q + q` halves to `d ≤ blockRight q j`. -/
lemma le_blockRight_of (q d j : ℕ) (h : 2 * d ≤ 4 * (j + 1) * q + q) :
    (d : ℝ) ≤ blockRight q j := by
  have hcast : ((2 * d : ℕ) : ℝ) ≤ ((4 * (j + 1) * q + q : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at hcast
  unfold blockRight
  have key : 2 * ((j : ℝ) + 1) * (q : ℝ) + (q : ℝ) / 2
      = ((4 * ((j : ℝ) + 1) * (q : ℝ)) + (q : ℝ)) / 2 := by ring
  rw [key, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- **Block membership.** The doubled integer spacing is equivalent to the
real block interval `blockLeft q j < d ≤ blockRight q j`. -/
lemma mem_block_iff (q d j : ℕ) :
    (4 * j * q + q < 2 * d ∧ 2 * d ≤ 4 * (j + 1) * q + q)
      ↔ blockLeft q j < (d : ℝ) ∧ (d : ℝ) ≤ blockRight q j := by
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨blockLeft_lt_of q d j h1, le_blockRight_of q d j h2⟩
  · intro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have hR : ((4 * j * q + q : ℕ) : ℝ) < ((2 * d : ℕ) : ℝ) := by
        push_cast
        unfold blockLeft at h1
        linarith [h1]
      exact_mod_cast hR
    · have hR : ((2 * d : ℕ) : ℝ) ≤ ((4 * (j + 1) * q + q : ℕ) : ℝ) := by
        push_cast
        unfold blockRight at h2
        linarith [h2]
      exact_mod_cast hR

end TaoFivePrimesBlock
