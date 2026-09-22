import Definitions.Def_MagicSquaresMatchingBoundary

/-!
# The easy branch of the finite matching-boundary criterion

When the selected permutation support `φ` is already contained in `D`, every
candidate containing `D` must equal `B`.  Thus its weighted boundary sum is
the single coefficient at `B`.  No matching-coverage assumption is needed.
-/

set_option autoImplicit false

namespace MagicSquaresBoundary

open Finset

theorem fiberCandidates_filter_eq_singleton_of_subset {n : ℕ}
    {B φ D : Finset (Fin n × Fin n)} (hDB : D ⊆ B) (hφD : φ ⊆ D) :
    (fiberCandidates B φ).filter (fun C => D ⊆ C) = {B} := by
  classical
  ext C
  simp only [mem_filter, mem_singleton]
  constructor
  · rintro ⟨hC, hDC⟩
    rw [fiberCandidates, mem_filter, mem_powerset] at hC
    obtain ⟨hCB, hBφC⟩ := hC
    apply Subset.antisymm hCB
    intro e heB
    by_cases heφ : e ∈ φ
    · exact hDC (hφD heφ)
    · exact hBφC (mem_sdiff.mpr ⟨heB, heφ⟩)
  · intro hCB
    subst C
    constructor
    · rw [fiberCandidates, mem_filter, mem_powerset]
      exact ⟨Subset.rfl, sdiff_subset⟩
    · exact hDB

theorem sum_fiberCandidates_filter_of_perm_subset {n : ℕ}
    {B φ D : Finset (Fin n × Fin n)} (hDB : D ⊆ B) (hφD : φ ⊆ D)
    (w : Finset (Fin n × Fin n) → ℚ) :
    (∑ C ∈ (fiberCandidates B φ).filter (fun C => D ⊆ C), w C) = w B := by
  rw [fiberCandidates_filter_eq_singleton_of_subset hDB hφD]
  simp

/-- The `φ ⊆ D` branch of `MatchingBoundaryCriterion` is therefore automatic.
The remaining branch is the genuinely nontrivial cancellation when `φ ⊈ D`. -/
theorem matchingBoundaryCriterion_easy_case {n : ℕ}
    {B D : Finset (Fin n × Fin n)} (σ : Equiv.Perm (Fin n))
    (hDB : D ⊆ B) (hφD : permSupport σ ⊆ D) :
    (∑ C ∈ (fiberCandidates B (permSupport σ)).filter
      (fun C => D ⊆ C), matchingEulerCoefficient n C) =
      matchingEulerCoefficient n B :=
  sum_fiberCandidates_filter_of_perm_subset hDB hφD (matchingEulerCoefficient n)

end MagicSquaresBoundary
