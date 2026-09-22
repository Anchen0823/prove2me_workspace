import examples.«magic-squares».spencer.ClosedSupport
import examples.«magic-squares».spencer.ClosedSupportIE
import examples.«magic-squares».spencer.PolynomialRecurrence
import examples.«magic-squares».spencer.S5Bridge

/-!
# Closed-support induction, including line sum zero

Subtract a fixed supported permutation from squares positive on that permutation.
The complement is a union of zero-cell conditions. Inclusion-exclusion expresses
its size using strictly smaller boards at the new, positive level. Boards with
no permutation vanish there, so their exceptional zero matrix causes no problem.
Discrete summation starts at the actual level zero, closing the earlier S5 gap.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace MagicSquaresSpencer

open Finset Polynomial MagicSquares

theorem closedFiber_card_recurrence (n t : ℕ) (B : Finset (Fin n × Fin n))
    (σ : Equiv.Perm (Fin n)) (hφB : matSupport (permMatrix σ) ⊆ B) :
    ((closedFiber n (t + 1) B).card : ℚ) = (closedFiber n t B).card +
      ∑ S ∈ (matSupport (permMatrix σ)).powerset.filter (·.Nonempty),
        (-1 : ℚ) ^ (S.card + 1) * (closedFiber n (t + 1) (B \ S)).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := closedFiber n (t + 1) B) (fun M => matSupport (permMatrix σ) ⊆ matSupport M)
  rw [card_closedFiber_filter_permSupport n t B σ hφB] at hsplit
  have hIE := card_filter_subset_not_subset_eq_sum_card_filter_subset_sdiff
    (matBoxLine n (t + 1)) matSupport B (matSupport (permMatrix σ))
  have hfilter : (closedFiber n (t + 1) B).filter
      (fun M => ¬ matSupport (permMatrix σ) ⊆ matSupport M) =
      (matBoxLine n (t + 1)).filter (fun M => matSupport M ⊆ B ∧
        ¬ matSupport (permMatrix σ) ⊆ matSupport M) := by
    simp [closedFiber, Finset.filter_filter]
  rw [← hfilter] at hIE
  change (((closedFiber n (t + 1) B).filter
    (fun M => ¬ matSupport (permMatrix σ) ⊆ matSupport M)).card : ℚ) = _ at hIE
  have hcast := congrArg (fun k : ℕ => (k : ℚ)) hsplit
  push_cast at hcast
  rw [hIE] at hcast
  exact hcast.symm

def HasPerm (n : ℕ) (B : Finset (Fin n × Fin n)) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), matSupport (permMatrix σ) ⊆ B

noncomputable def boardPerm (n : ℕ) (B : Finset (Fin n × Fin n)) : Equiv.Perm (Fin n) := by
  classical
  exact if h : HasPerm n B then Classical.choose h else Equiv.refl _

theorem boardPerm_subset {n : ℕ} {B : Finset (Fin n × Fin n)} (h : HasPerm n B) :
    matSupport (permMatrix (boardPerm n B)) ⊆ B := by
  simp only [boardPerm, dif_pos h]
  exact Classical.choose_spec h

noncomputable def closedTerms (n : ℕ) (B : Finset (Fin n × Fin n)) :
    Finset (Finset (Fin n × Fin n)) := by
  classical
  exact (B ∩ matSupport (permMatrix (boardPerm n B))).powerset.filter (·.Nonempty)

theorem exists_polynomial_closedFiber (n : ℕ) (B : Finset (Fin n × Fin n))
    (hB : HasPerm n B) :
    ∃ P : Polynomial ℚ, ∀ t : ℕ, P.eval (t : ℚ) = (closedFiber n t B).card := by
  classical
  apply exists_poly_of_board_recurrence
    (fun C t => ((closedFiber n t C).card : ℚ)) (HasPerm n) (closedTerms n)
    (fun C S => C \ S) (fun _ S => (-1 : ℚ) ^ (S.card + 1)) ?_ ?_ ?_ B hB
  · intro C S hS
    have h := Finset.mem_filter.mp hS
    have hsub := Finset.mem_powerset.mp h.1
    exact Finset.sdiff_ssubset (hsub.trans Finset.inter_subset_left) h.2
  · intro C hno t
    rw [closedFiber_eq_empty_of_no_perm (by omega)
      (fun σ hσ => hno ⟨σ, hσ⟩), Finset.card_empty, Nat.cast_zero]
  · intro C hC t
    have hperm := boardPerm_subset hC
    have hterms : closedTerms n C =
        (matSupport (permMatrix (boardPerm n C))).powerset.filter (·.Nonempty) := by
      simp only [closedTerms, Finset.inter_eq_right.mpr hperm]
    rw [hterms]
    exact closedFiber_card_recurrence n t C (boardPerm n C) hperm

/-- Polynomiality on every natural line sum, with no unproved zero-point input. -/
theorem exists_polynomial_semiMagicCount_all (n : ℕ) :
    ∃ P : Polynomial ℚ, ∀ t : ℕ, P.eval (t : ℚ) = (semiMagicCount n t : ℚ) := by
  obtain ⟨P, hP⟩ := exists_polynomial_closedFiber n Finset.univ
    ⟨Equiv.refl _, Finset.subset_univ _⟩
  exact ⟨P, fun t => by rw [hP t, card_closedFiber_univ]⟩

theorem sum_sB_eq_one (n : ℕ) : ∑ B ∈ supportSet n, sB n B = 1 :=
  (sum_sB_eq_one_iff_exists_polynomial_semiMagicCount n).mpr
    (exists_polynomial_semiMagicCount_all n)

/-- The polynomial-existence milestone, with the previously proved exact degree. -/
theorem exists_polynomial_semiMagicCount_all_degree_eq (n : ℕ) (hn : 1 ≤ n) :
    ∃ P : Polynomial ℚ, P.natDegree = (n - 1) ^ 2 ∧
      ∀ t : ℕ, P.eval (t : ℚ) = (semiMagicCount n t : ℚ) :=
  exists_polynomial_semiMagicCount_degree_eq_of_sum_sB n hn (sum_sB_eq_one n)

end MagicSquaresSpencer
