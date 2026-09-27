import Theorems.Thm_NoAdjString_mem_noAdjacentStringsCard
import Theorems.Thm_NoAdjString_card_noAdjacentStringsCard
import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function NoAdjString

theorem solution (n : ℕ) :
    (noAdjacentStrings n).card =
      ∑ k ∈ Finset.range (n + 1), Nat.choose (n + 1 - k) k := by
  have hpart : noAdjacentStrings n =
      Finset.biUnion (Finset.range (n + 1)) (fun k => noAdjacentStringsCard n k) := by
    ext f
    simp only [noAdjacentStrings, noAdjacentStringsCard, Finset.mem_biUnion,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hna
      have hk : (supportFinset f).card ≤ n := by
        simpa using Finset.card_le_univ (s := supportFinset f)
      exact ⟨(supportFinset f).card, Finset.mem_range.mpr (by omega), hna, rfl⟩
    · rintro ⟨k, _, hna, _⟩
      exact hna
  rw [hpart, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (fun k _ => card_noAdjacentStringsCard n k)]
  · intro i _ j _ hne
    simp only [Finset.disjoint_left]
    intro f hi hj
    have hci : (supportFinset f).card = i := (mem_noAdjacentStringsCard.mp hi).2
    have hcj : (supportFinset f).card = j := (mem_noAdjacentStringsCard.mp hj).2
    omega
