import Theorems.Thm_NoAdjString_noAdjacentOnes_iff_noAdjacent
import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function NoAdjString

theorem solution (n : ℕ) :
    (noAdjacentStrings n).image (boolFinsetEquiv n) = noAdjacentFinset n := by
  ext s
  simp only [Finset.mem_image, noAdjacentStrings, noAdjacentFinset, mem_filter]
  constructor
  · rintro ⟨f, ⟨_, hna⟩, rfl⟩
    exact ⟨Finset.mem_univ _, (noAdjacentOnes_iff_noAdjacent f).mp hna⟩
  · rintro ⟨_, hna⟩
    let f : Fin n → Bool := (boolFinsetEquiv n).symm s
    have he : (boolFinsetEquiv n) f = s := (boolFinsetEquiv n).apply_symm_apply s
    have hfs : supportFinset f = s := by
      change (boolFinsetEquiv n) f = s; exact he
    have hn : NoAdjacentOnes f := by
      rw [noAdjacentOnes_iff_noAdjacent f, hfs]; exact hna
    exact ⟨f, ⟨Finset.mem_univ f, hn⟩, he⟩
