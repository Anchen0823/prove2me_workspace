import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function

theorem solution {n k : ℕ} {f : Fin n → Bool} :
    f ∈ noAdjacentStringsCard n k ↔
      NoAdjacentOnes f ∧ (supportFinset f).card = k := by
  simp [noAdjacentStringsCard, noAdjacentStrings]
