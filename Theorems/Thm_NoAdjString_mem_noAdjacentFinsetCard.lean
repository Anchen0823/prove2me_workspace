import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function

namespace NoAdjString

theorem mem_noAdjacentFinsetCard {n k : ℕ} {s : Finset (Fin n)} :
    s ∈ noAdjacentFinsetCard n k ↔ s.noAdjacent ∧ s.card = k := by sorry

end NoAdjString
