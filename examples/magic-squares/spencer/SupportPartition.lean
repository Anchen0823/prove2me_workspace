import examples.«magic-squares».spencer.ClosedSupport
import examples.«magic-squares».spencer.Aggregate

set_option autoImplicit false

open Finset

namespace MagicSquaresSpencer

/-- A closed-support fibre is the disjoint union of exact-support fibres indexed by its
subboards. -/
theorem card_closedFiber_eq_sum_matFiber (n t : ℕ)
    (B : Finset (Fin n × Fin n)) :
    (closedFiber n t B).card =
      ∑ C ∈ B.powerset, (matFiber n t t C).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := matSupport) (s := closedFiber n t B)
    (t := B.powerset) (fun M hM => Finset.mem_powerset.mpr
      (mem_closedFiber.mp hM).2)]
  apply Finset.sum_congr rfl
  intro C hC
  have hCB : C ⊆ B := Finset.mem_powerset.mp hC
  congr 1
  ext M
  rw [matFiber_eq_filter_matBoxLine C]
  simp only [Finset.mem_filter, mem_closedFiber]
  constructor
  · rintro ⟨⟨hline, _⟩, hsup⟩
    exact ⟨hline, hsup⟩
  · rintro ⟨hline, hsup⟩
    exact ⟨⟨hline, hsup ▸ hCB⟩, hsup⟩

/-- Rational-cast form for polynomial and Möbius-inversion calculations. -/
theorem card_closedFiber_eq_sum_matFiber_rat (n t : ℕ)
    (B : Finset (Fin n × Fin n)) :
    ((closedFiber n t B).card : ℚ) =
      ∑ C ∈ B.powerset, ((matFiber n t t C).card : ℚ) := by
  exact_mod_cast card_closedFiber_eq_sum_matFiber n t B

end MagicSquaresSpencer
