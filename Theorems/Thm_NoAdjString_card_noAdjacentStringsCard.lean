import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function

namespace NoAdjString

theorem card_noAdjacentStringsCard (n k : ℕ) :
    (noAdjacentStringsCard n k).card = Nat.choose (n + 1 - k) k := by sorry

end NoAdjString
