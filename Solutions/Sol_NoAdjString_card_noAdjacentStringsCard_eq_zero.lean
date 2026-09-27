import Theorems.Thm_NoAdjString_card_noAdjacentStringsCard
import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function NoAdjString

theorem solution (n k : ℕ) (h : n + 1 < 2 * k) :
    (noAdjacentStringsCard n k).card = 0 := by
  rw [card_noAdjacentStringsCard]
  exact Nat.choose_eq_zero_of_lt (by omega)
