import Definitions.Def_NoAdjacentBinaryStrings
import Mathlib.Data.Nat.Fib.Basic

open Finset Function

namespace NoAdjString

theorem sum_choose_pascal_diagonal (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Nat.choose (n + 1 - k) k = Nat.fib (n + 2) := by sorry

end NoAdjString
