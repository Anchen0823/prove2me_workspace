import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function

theorem solution {n : ℕ} (f : Fin n → Bool) :
    NoAdjacentOnes f ↔ (supportFinset f).noAdjacent := by
  simp only [NoAdjacentOnes, Finset.noAdjacent, supportFinset, mem_filter]
  constructor
  · intro h x ⟨_, hfx⟩ hnext ⟨_, hfnext⟩
    exact h x hnext ⟨hfx, hfnext⟩
  · intro h i hnext ⟨hfi, hfnext⟩
    exact h i ⟨Finset.mem_univ i, hfi⟩ hnext
      ⟨Finset.mem_univ _, hfnext⟩
