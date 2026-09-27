import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function

namespace NoAdjString

theorem mem_noAdjacentStringsCard {n k : ℕ} {f : Fin n → Bool} :
    f ∈ noAdjacentStringsCard n k ↔
      NoAdjacentOnes f ∧ (supportFinset f).card = k := by sorry

end NoAdjString
