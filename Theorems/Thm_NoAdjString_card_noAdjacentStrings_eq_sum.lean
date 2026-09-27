import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function

namespace NoAdjString

theorem card_noAdjacentStrings_eq_sum (n : ℕ) :
    (noAdjacentStrings n).card =
      ∑ k ∈ Finset.range (n + 1), Nat.choose (n + 1 - k) k := by sorry

end NoAdjString
