import Definitions.Def_NoAdjacentGapEquiv

open Finset Function

namespace NoAdjString

theorem card_noAdjacentFinsetCard (n k : ℕ) :
    (noAdjacentFinsetCard n k).card = Nat.choose (n + 1 - k) k := by sorry

end NoAdjString
