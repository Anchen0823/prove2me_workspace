import Theorems.Thm_NoAdjString_noAdjacentOnes_iff_noAdjacent
import Theorems.Thm_NoAdjString_mem_noAdjacentStringsCard
import Theorems.Thm_NoAdjString_mem_noAdjacentFinsetCard
import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function NoAdjString

theorem solution (n k : ℕ) :
    (noAdjacentStringsCard n k).image (boolFinsetEquiv n) = noAdjacentFinsetCard n k := by
  ext s
  simp only [Finset.mem_image, mem_noAdjacentStringsCard, mem_noAdjacentFinsetCard]
  constructor
  · rintro ⟨f, ⟨hna, hk⟩, rfl⟩
    have h : (supportFinset f).noAdjacent := (noAdjacentOnes_iff_noAdjacent f).mp hna
    exact ⟨h, hk⟩
  · rintro ⟨hna, hk⟩
    let f : Fin n → Bool := (boolFinsetEquiv n).symm s
    have he : (boolFinsetEquiv n) f = s := (boolFinsetEquiv n).apply_symm_apply s
    have hfs : supportFinset f = s := by
      change (boolFinsetEquiv n) f = s; exact he
    have hn : NoAdjacentOnes f := by
      rw [noAdjacentOnes_iff_noAdjacent f, hfs]; exact hna
    have hk' : (supportFinset f).card = k := by rw [hfs]; exact hk
    exact ⟨f, ⟨hn, hk'⟩, he⟩
