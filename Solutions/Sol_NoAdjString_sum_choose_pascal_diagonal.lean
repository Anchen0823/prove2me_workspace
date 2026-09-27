import Theorems.Thm_NoAdjString_card_noAdjacentStrings_eq_sum
import Theorems.Thm_NoAdjString_card_noAdjacentStrings
import Definitions.Def_NoAdjacentBinaryStrings
import Mathlib.Data.Nat.Fib.Basic

open Finset Function NoAdjString

theorem solution (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Nat.choose (n + 1 - k) k = Nat.fib (n + 2) := by
  rw [←card_noAdjacentStrings_eq_sum, card_noAdjacentStrings]
