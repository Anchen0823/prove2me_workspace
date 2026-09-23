import examples.«magic-squares».spencer.FiniteMobiusWeights

set_option autoImplicit false

namespace MagicSquaresGeometry

open Finset
attribute [local instance] Classical.propDecidable

/-- An order isomorphism preserves Möbius weights from bottom. -/
theorem mobius_from_bottom_orderIso {α β : Type*}
    [Fintype α] [PartialOrder α] [OrderBot α] [LocallyFiniteOrder α] [DecidableEq α]
    [Fintype β] [PartialOrder β] [OrderBot β] [LocallyFiniteOrder β] [DecidableEq β]
    (e : α ≃o β) (b : α) :
    IncidenceAlgebra.mu ℚ ⊥ (e b) = IncidenceAlgebra.mu ℚ ⊥ b := by
  classical
  have hprefix (c : α) :
      (∑ x ∈ (Finset.univ : Finset α).filter (fun x => x ≤ c),
        IncidenceAlgebra.mu ℚ ⊥ (e x)) =
        if c = ⊥ then 1 else 0 := by
    have hsum :
        (∑ x ∈ (Finset.univ : Finset α).filter (fun x => x ≤ c),
          IncidenceAlgebra.mu ℚ ⊥ (e x)) =
        ∑ y ∈ (Finset.univ : Finset β).filter (fun y => y ≤ e c),
          IncidenceAlgebra.mu ℚ ⊥ y := by
      apply Finset.sum_equiv e.toEquiv
      · intro x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (e.le_iff_le).symm
      · intro x hx
        rfl
    rw [hsum]
    have hset :
        (Finset.univ : Finset β).filter (fun y => y ≤ e c) =
          Finset.Icc (⊥ : β) (e c) := by
      ext y
      simp
    rw [hset, IncidenceAlgebra.sum_Icc_mu_right]
    by_cases hc : c = ⊥
    · subst c
      simp
    · have hne : (⊥ : β) ≠ e c := by
        intro he
        apply hc
        apply e.injective
        simpa [e.map_bot] using he.symm
      simp [hc, hne]
  exact weights_eq_mobius_from_bottom
    (fun x : α => IncidenceAlgebra.mu ℚ ⊥ (e x)) hprefix b

end MagicSquaresGeometry
