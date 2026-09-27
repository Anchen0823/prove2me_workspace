import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function

theorem solution {n k : ℕ} {s : Finset (Fin n)} :
    s ∈ noAdjacentFinsetCard n k ↔ s.noAdjacent ∧ s.card = k := by
  simp [noAdjacentFinsetCard, noAdjacentFinset]
