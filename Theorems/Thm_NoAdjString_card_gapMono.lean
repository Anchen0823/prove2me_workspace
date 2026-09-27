import Definitions.Def_NoAdjacentGapEquiv

open Finset Function

namespace NoAdjString

theorem card_gapMono (n k : ℕ) :
    Fintype.card (GapMono n k) = Nat.choose (n + 1 - k) k := by sorry

end NoAdjString
