import Definitions.Def_NoAdjacentGapEquiv
import Mathlib.Data.Nat.Fib.Basic

open Finset Function

namespace NoAdjString

theorem card_noAdjacentStrings (n : ℕ) :
    (noAdjacentStrings n).card = Nat.fib (n + 2) := by sorry

end NoAdjString
