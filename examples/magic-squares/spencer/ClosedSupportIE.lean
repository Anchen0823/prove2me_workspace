import Mathlib.Combinatorics.Enumerative.InclusionExclusion

set_option autoImplicit false
open Finset

theorem card_filter_subset_not_subset_eq_sum_card_filter_subset_sdiff
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (A : Finset α) (supp : α → Finset ι) (B φ : Finset ι) :
    ((A.filter (fun x => supp x ⊆ B ∧ ¬ φ ⊆ supp x)).card : ℚ) =
      ∑ S ∈ φ.powerset.filter (·.Nonempty),
        (-1 : ℚ) ^ (S.card + 1) *
          ((A.filter (fun x => supp x ⊆ B \ S)).card : ℚ) := by
  classical
  let U : Finset α := A.filter (fun x => supp x ⊆ B)
  let F : ι → Finset α := fun i => U.filter (fun x => i ∉ supp x)
  have hIE := Finset.inclusion_exclusion_card_biUnion φ F
  have hcard : φ.biUnion F = A.filter (fun x => supp x ⊆ B ∧ ¬ φ ⊆ supp x) := by
    ext x
    simp only [mem_biUnion, mem_filter, F, U]
    constructor
    · rintro ⟨i, hi, ⟨hA, hB⟩, hni⟩
      exact ⟨hA, hB, fun h => hni (h hi)⟩
    · rintro ⟨hA, hB, hnot⟩
      obtain ⟨i, hi, hni⟩ := Finset.not_subset.mp hnot
      exact ⟨i, hi, ⟨hA, hB⟩, hni⟩
  rw [hcard] at hIE
  have hIEq :
      ((A.filter (fun x => supp x ⊆ B ∧ ¬ φ ⊆ supp x)).card : ℚ) =
        ∑ S : φ.powerset.filter (·.Nonempty),
          (-1 : ℚ) ^ (S.1.card + 1) *
            ((S.1.inf' (Finset.mem_filter.mp S.2).2 F).card : ℚ) := by
    exact_mod_cast hIE
  calc
    ((A.filter (fun x => supp x ⊆ B ∧ ¬ φ ⊆ supp x)).card : ℚ) =
        ∑ S : φ.powerset.filter (·.Nonempty),
          (-1 : ℚ) ^ (S.1.card + 1) *
            ((S.1.inf' (Finset.mem_filter.mp S.2).2 F).card : ℚ) := hIEq
    _ = ∑ S ∈ φ.powerset.filter (·.Nonempty),
          (-1 : ℚ) ^ (S.card + 1) *
            ((A.filter (fun x => supp x ⊆ B \ S)).card : ℚ) := by
      conv_rhs => rw [← Finset.sum_attach]
      push_cast
      apply Finset.sum_congr rfl
      intro S hS
      rw [show ((S.1.inf' (Finset.mem_filter.mp S.2).2 F).card : ℚ) =
          ((A.filter (fun x => supp x ⊆ B \ S.1)).card : ℚ) by
        norm_cast
        apply congrArg Finset.card
        ext x
        simp only [mem_inf', mem_filter, F, U]
        constructor
        · intro hxi
          obtain ⟨i, hi⟩ := (Finset.mem_filter.mp S.2).2
          have hbase := (hxi i hi).1
          refine ⟨hbase.1, ?_⟩
          intro j hj
          exact Finset.mem_sdiff.mpr ⟨hbase.2 hj, fun hjS => (hxi j hjS).2 hj⟩
        · rintro ⟨hxA, hsub⟩
          intro i hi
          refine ⟨⟨hxA, ?_⟩, ?_⟩
          · intro j hj
            exact (Finset.mem_sdiff.mp (hsub hj)).1
          · intro hix
            exact (Finset.mem_sdiff.mp (hsub hix)).2 hi]
