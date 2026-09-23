import Mathlib

set_option autoImplicit false

namespace MagicSquaresEuler

open Finset

/-- A finite set has a right neighborhood of `r` containing no member strictly
between `r` and its endpoint. -/
theorem exists_right_gap (S : Finset ℝ) (r : ℝ) :
    ∃ t : ℝ, r < t ∧ ∀ s ∈ S, r < s → t < s := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨r + 1, by linarith, ?_⟩
    simp
  | @insert s S hs ih =>
    obtain ⟨t, hrt, ht⟩ := ih
    by_cases hrs : r < s
    · refine ⟨min t ((r + s) / 2), lt_min hrt (by linarith), ?_⟩
      intro u hu hru
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
      · exact lt_of_le_of_lt (min_le_left _ _) (ht u hu hru)
    · refine ⟨t, hrt, ?_⟩
      intro u hu hru
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact False.elim (hrs hru)
      · exact ht u hu hru

end MagicSquaresEuler
