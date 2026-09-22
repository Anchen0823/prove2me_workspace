import examples.«magic-squares».spencer.Recursion
import examples.«magic-squares».spencer.Aggregate

/-!
# Closed support fibres

These are semi-magic squares whose support is contained in a fixed board.  Subtracting a fixed
permutation matrix is a bijection between the next-level squares positive on that permutation and
the entire current-level closed fibre.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset

namespace MagicSquaresSpencer

open MagicSquares

variable {n : ℕ}

/-- Semi-magic squares of line sum `t` whose support is contained in `B`. -/
noncomputable def closedFiber (n t : ℕ) (B : Finset (Fin n × Fin n)) :
    Finset (Matrix (Fin n) (Fin n) ℕ) := by
  classical
  exact (matBoxLine n t).filter fun M => matSupport M ⊆ B

theorem mem_closedFiber {n t : ℕ} {B : Finset (Fin n × Fin n)}
    {M : Matrix (Fin n) (Fin n) ℕ} :
    M ∈ closedFiber n t B ↔ M ∈ matBoxLine n t ∧ matSupport M ⊆ B := by
  classical
  simp [closedFiber]

/-- Containing the support of a permutation is exactly positivity on its selected cells. -/
theorem permSupport_subset_matSupport_iff (M : Matrix (Fin n) (Fin n) ℕ)
    (σ : Equiv.Perm (Fin n)) :
    matSupport (permMatrix σ) ⊆ matSupport M ↔ ∀ i, 0 < M i (σ i) := by
  constructor
  · intro h i
    have := h (mem_matSupport_permMatrix_self σ i)
    simpa [matSupport] using this
  · intro h
    rw [matSupport_permMatrix]
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    simpa [matSupport] using h i

/-- Subtracting `Pσ` bijects closed-support squares at level `t+1` which are positive on `σ`
with all closed-support squares at level `t`. -/
theorem card_closedFiber_filter_permSupport (n t : ℕ)
    (B : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n))
    (hφB : matSupport (permMatrix σ) ⊆ B) :
    ((closedFiber n (t + 1) B).filter
        (fun M => matSupport (permMatrix σ) ⊆ matSupport M)).card
      = (closedFiber n t B).card := by
  classical
  refine Finset.card_bij (fun T _ => T - permMatrix σ) ?_ ?_ ?_
  · intro T hT
    rw [Finset.mem_filter] at hT
    obtain ⟨hclosed, hφT⟩ := hT
    rw [mem_closedFiber] at hclosed ⊢
    obtain ⟨hline, hTB⟩ := hclosed
    rw [matBoxLine, Finset.mem_filter] at hline ⊢
    obtain ⟨hbox, hls⟩ := hline
    have hpos : ∀ i, 0 < T i (σ i) :=
      (permSupport_subset_matSupport_iff T σ).mp hφT
    refine ⟨?_, matSupport_sub_permMatrix_subset T σ hpos |>.trans hTB⟩
    refine ⟨?_, ?_⟩
    · rw [mem_matBox]
      exact fun i j => le_of_rowSum (fun i => by
        rw [sum_sub_permMatrix T σ hpos i, hls.1 i]
        omega) i j
    · exact ⟨fun i => by rw [sum_sub_permMatrix T σ hpos i, hls.1 i]; omega,
        fun j => by rw [sum_sub_permMatrix_col T σ hpos j, hls.2 j]; omega⟩
  · intro T₁ hT₁ T₂ hT₂ heq
    rw [Finset.mem_filter] at hT₁ hT₂
    have hpos₁ := (permSupport_subset_matSupport_iff T₁ σ).mp hT₁.2
    have hpos₂ := (permSupport_subset_matSupport_iff T₂ σ).mp hT₂.2
    rw [← sub_add_permMatrix T₁ σ hpos₁, ← sub_add_permMatrix T₂ σ hpos₂, heq]
  · intro S hS
    refine ⟨S + permMatrix σ, ?_, ?_⟩
    · rw [Finset.mem_filter, mem_closedFiber]
      rw [mem_closedFiber] at hS
      obtain ⟨hline, hSB⟩ := hS
      rw [matBoxLine, Finset.mem_filter] at hline
      obtain ⟨hbox, hls⟩ := hline
      have hline' : S + permMatrix σ ∈ matBoxLine n (t + 1) := by
        rw [matBoxLine, Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · rw [mem_matBox]
          exact fun i j => le_of_rowSum (fun i => by
            rw [sum_add_permMatrix S σ i, hls.1 i]) i j
        · exact ⟨fun i => by rw [sum_add_permMatrix S σ i, hls.1 i],
            fun j => by rw [sum_add_permMatrix_col S σ j, hls.2 j]⟩
      refine ⟨⟨hline', ?_⟩, ?_⟩
      · rw [matSupport_add]
        exact Finset.union_subset hSB hφB
      · rw [matSupport_add]
        exact Finset.subset_union_right
    · exact add_sub_permMatrix S σ

/-- If `B` contains no permutation support, its positive closed fibres are empty. -/
theorem closedFiber_eq_empty_of_no_perm {n t : ℕ} (ht : 1 ≤ t)
    {B : Finset (Fin n × Fin n)}
    (hno : ∀ σ : Equiv.Perm (Fin n), ¬ matSupport (permMatrix σ) ⊆ B) :
    closedFiber n t B = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro M hM
  rw [mem_closedFiber] at hM
  rw [matBoxLine, Finset.mem_filter] at hM
  obtain ⟨σ, hσ⟩ := exists_perm_support_subset_of_lineSums ht hM.1.2
  exact hno σ (hσ.trans hM.2)

/-- The full board imposes no support restriction. -/
theorem closedFiber_univ (n t : ℕ) :
    closedFiber n t (Finset.univ : Finset (Fin n × Fin n)) = matBoxLine n t := by
  classical
  ext M
  simp [closedFiber]

theorem card_closedFiber_univ (n t : ℕ) :
    (closedFiber n t (Finset.univ : Finset (Fin n × Fin n))).card =
      MagicSquares.semiMagicCount n t := by
  rw [closedFiber_univ, card_matBoxLine]

end MagicSquaresSpencer
