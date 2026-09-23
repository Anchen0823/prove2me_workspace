import Mathlib

set_option autoImplicit false

namespace MagicSquaresGeometry

open Finset
attribute [local instance] Classical.propDecidable

/-- The weights with a unit prefix only at bottom are uniquely the Möbius
weights from bottom. -/
theorem weights_eq_mobius_from_bottom {α : Type*} [Fintype α]
    [PartialOrder α] [OrderBot α] [LocallyFiniteOrder α] [DecidableEq α]
    (w : α → ℚ)
    (hprefix : ∀ b : α,
      (∑ x ∈ (Finset.univ : Finset α).filter (fun x => x ≤ b), w x) =
        if b = ⊥ then 1 else 0) :
    ∀ b : α, w b = IncidenceAlgebra.mu ℚ ⊥ b := by
  classical
  have hp (b : α) :
      (∑ x ∈ Finset.Icc (⊥ : α) b, w x) =
        if b = ⊥ then 1 else 0 := by
    convert hprefix b using 1
    congr 1
    ext x
    simp
  intro b
  induction b using (wellFounded_lt (α := α)).induction with
  | h b ih =>
    have hmu := IncidenceAlgebra.sum_Icc_mu_right (𝕜 := ℚ) (⊥ : α) b
    have hsum :
        (∑ x ∈ Finset.Icc (⊥ : α) b,
          (w x - IncidenceAlgebra.mu ℚ ⊥ x)) = 0 := by
      rw [Finset.sum_sub_distrib, hp b, hmu]
      simp [eq_comm]
    have hsingle :
        (∑ x ∈ Finset.Icc (⊥ : α) b,
          (w x - IncidenceAlgebra.mu ℚ ⊥ x)) =
          w b - IncidenceAlgebra.mu ℚ ⊥ b := by
      apply Finset.sum_eq_single_of_mem b
      · simp
      · intro x hx hxb
        have hxb' : x ≤ b := (Finset.mem_Icc.mp hx).2
        rw [ih x (lt_of_le_of_ne hxb' hxb), sub_self]
    exact sub_eq_zero.mp (hsingle.symm.trans hsum)

end MagicSquaresGeometry
