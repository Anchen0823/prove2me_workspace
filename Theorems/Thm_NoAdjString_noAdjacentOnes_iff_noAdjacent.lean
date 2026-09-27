import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function

namespace NoAdjString

theorem noAdjacentOnes_iff_noAdjacent {n : ℕ} (f : Fin n → Bool) :
    NoAdjacentOnes f ↔ (supportFinset f).noAdjacent := by sorry

end NoAdjString
