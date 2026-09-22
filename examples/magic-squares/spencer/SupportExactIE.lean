import examples.«magic-squares».spencer.ClosedSupportIE

set_option autoImplicit false

open Finset

theorem card_filter_eq_support_eq_sum_subset_sdiff
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (A : Finset α) (supp : α → Finset ι) (B : Finset ι) :
    ((A.filter (fun x => supp x = B)).card : ℚ) =
      ∑ S ∈ B.powerset,
        (-1 : ℚ) ^ S.card *
          ((A.filter (fun x => supp x ⊆ B \ S)).card : ℚ) := by
  classical
  have hIE := card_filter_subset_not_subset_eq_sum_card_filter_subset_sdiff
    A supp B B
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := A.filter (fun x => supp x ⊆ B)) (fun x => B ⊆ supp x)
  have hnon :
      ((A.filter (fun x => supp x ⊆ B ∧ ¬ B ⊆ supp x)).card : ℚ) =
        ∑ S ∈ B.powerset.filter (·.Nonempty),
          (-1 : ℚ) ^ (S.card + 1) *
            ((A.filter (fun x => supp x ⊆ B \ S)).card : ℚ) := hIE
  have hsplitQ :
      ((A.filter (fun x => supp x ⊆ B ∧ B ⊆ supp x)).card : ℚ) +
        ((A.filter (fun x => supp x ⊆ B ∧ ¬ B ⊆ supp x)).card : ℚ) =
          ((A.filter (fun x => supp x ⊆ B)).card : ℚ) := by
    have hc := congrArg (fun k : ℕ => (k : ℚ)) hsplit
    simpa [Finset.filter_filter, and_comm, and_left_comm, and_assoc] using hc
  have heq : A.filter (fun x => supp x ⊆ B ∧ B ⊆ supp x) =
      A.filter (fun x => supp x = B) := by
    ext x
    simp [Finset.Subset.antisymm_iff]
  have hsplitQ' :
      ((A.filter (fun x => supp x = B)).card : ℚ) +
        ((A.filter (fun x => supp x ⊆ B ∧ ¬ B ⊆ supp x)).card : ℚ) =
          ((A.filter (fun x => supp x ⊆ B)).card : ℚ) := by
    rw [← heq]
    exact hsplitQ
  have hpow : B.powerset = {∅} ∪ B.powerset.filter (·.Nonempty) := by
    ext S
    simp only [mem_powerset, mem_union, mem_singleton, mem_filter]
    constructor
    · intro hSB
      by_cases h0 : S = ∅
      · exact Or.inl h0
      · exact Or.inr ⟨hSB, Finset.nonempty_iff_ne_empty.mpr h0⟩
    · rintro (rfl | ⟨hSB, _⟩)
      · simp
      · exact hSB
  rw [hpow, Finset.sum_union]
  · simp only [Finset.sum_singleton, Finset.card_empty, pow_zero, one_mul]
    rw [Finset.sdiff_empty]
    have hsplitQ'' := hsplitQ'
    rw [← hsplitQ'']
    have hsign :
        (∑ S ∈ B.powerset.filter (·.Nonempty),
          (-1 : ℚ) ^ S.card *
            ((A.filter (fun x => supp x ⊆ B \ S)).card : ℚ)) =
          -∑ S ∈ B.powerset.filter (·.Nonempty),
          (-1 : ℚ) ^ (S.card + 1) *
              ((A.filter (fun x => supp x ⊆ B \ S)).card : ℚ) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro S hS
      rw [pow_succ]
      ring
    rw [hsign, ← hnon]
    ring
  · simp [Finset.disjoint_left]
