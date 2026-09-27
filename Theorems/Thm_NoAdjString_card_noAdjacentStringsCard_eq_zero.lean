import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function

namespace NoAdjString

theorem card_noAdjacentStringsCard_eq_zero (n k : ℕ) (h : n + 1 < 2 * k) :
    (noAdjacentStringsCard n k).card = 0 := by sorry

end NoAdjString
