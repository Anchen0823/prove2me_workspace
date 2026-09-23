import Mathlib

set_option autoImplicit false

namespace MagicSquaresEuler

open Finset
attribute [local instance] Classical.propDecidable

/-- The alternating sum of the indicators of all intersections indexed by a
finite cover vanishes pointwise on the covered set. -/
theorem finiteCover_alternating_indicator_zero
    {α X : Type*} [DecidableEq α]
    (I : Finset α) (P : Set X) (F : α → Set X)
    (hcover : ∀ x ∈ P, ∃ i ∈ I, x ∈ F i) (x : X) :
    (∑ S ∈ I.powerset,
      if x ∈ P ∧ ∀ i ∈ S, x ∈ F i then (-1 : ℚ) ^ S.card else 0) = 0 := by
  classical
  by_cases hx : x ∈ P
  · let T : Finset α := I.filter fun i => x ∈ F i
    have hT : T.Nonempty := by
      obtain ⟨i, hiI, hiF⟩ := hcover x hx
      exact ⟨i, by simp [T, hiI, hiF]⟩
    have heq : I.powerset.filter (fun S => S ⊆ T) = T.powerset := by
      ext S
      simp only [mem_filter, mem_powerset]
      constructor
      · exact fun h => h.2
      · intro hST
        exact ⟨hST.trans (filter_subset _ _), hST⟩
    calc
      (∑ S ∈ I.powerset,
          if x ∈ P ∧ ∀ i ∈ S, x ∈ F i then (-1 : ℚ) ^ S.card else 0) =
          ∑ S ∈ I.powerset.filter (fun S => S ⊆ T), (-1 : ℚ) ^ S.card := by
            rw [sum_filter]
            apply sum_congr rfl
            intro S hSI
            have hiff : (∀ i ∈ S, x ∈ F i) ↔ S ⊆ T := by
              constructor
              · intro hSF i hiS
                exact mem_filter.mpr ⟨mem_powerset.mp hSI hiS, hSF i hiS⟩
              · intro hST i hiS
                exact (mem_filter.mp (hST hiS)).2
            simp only [hx, true_and, hiff]
      _ = ∑ S ∈ T.powerset, (-1 : ℚ) ^ S.card := by rw [heq]
      _ = 0 := by
        have hz := Finset.sum_powerset_neg_one_pow_card_of_nonempty hT
        exact_mod_cast hz
  · simp [hx]

end MagicSquaresEuler
