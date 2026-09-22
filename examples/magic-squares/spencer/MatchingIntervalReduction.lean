import examples.«magic-squares».spencer.MatchingCore
import examples.«magic-squares».spencer.MatchingCoefficientSupport
import examples.«magic-squares».spencer.MatchingBoundaryEasyCase
import examples.«magic-squares».spencer.WeightedWeisner

set_option autoImplicit false

namespace MagicSquaresBoundary
open Finset
attribute [local instance] Classical.propDecidable

/-- The still-unproved Euler relation for nondegenerate matching-support intervals. -/
def MatchingIntervalEuler (n : ℕ) : Prop :=
  ∀ D B : Finset (Fin n × Fin n), MatchingCoveredBoard n D →
    MatchingCoveredBoard n B → D ⊂ B →
      (∑ C ∈ B.powerset.filter (fun C => D ⊆ C), matchingEulerCoefficient n C) = 0

/-- The matching interval cancellation implies the finite boundary condition. -/
theorem matchingBoundaryCriterion_of_intervalEuler (n : ℕ) (hn : 1 ≤ n)
    (hEuler : MatchingIntervalEuler n) : MatchingBoundaryCriterion n := by
  classical
  intro B hB σ hσ D hD hDB
  let φ := permSupport σ
  by_cases hφD : φ ⊆ D
  · rw [if_pos hφD]
    exact matchingBoundaryCriterion_easy_case σ hDB hφD
  · rw [if_neg hφD]
    have hφB : φ ⊆ B := hσ
    have hA : D ∪ φ ⊆ B := union_subset hDB hφB
    have hw : ∀ C, ¬ MatchingCoveredBoard n C → matchingEulerCoefficient n C = 0 :=
      fun C hC => matchingEulerCoefficient_eq_zero_of_not_matchingCovered n hn C hC
    have hprefix (X : Finset (Fin n × Fin n))
        (hAX : D ∪ φ ⊆ X) (hXB : X ⊆ B) :
        (∑ C ∈ (Finset.univ : Finset (Finset (Fin n × Fin n))).filter
          (fun C => D ⊆ C ∧ C ⊆ X), matchingEulerCoefficient n C) = 0 := by
      have hφX : φ ⊆ X := subset_union_right.trans hAX
      have hDcore : D ⊆ matchingCore X :=
        (matchingCovered_subset_core_iff hD).mpr (subset_union_left.trans hAX)
      have hcoreCovered : MatchingCoveredBoard n (matchingCore X) :=
        matchingCore_matchingCovered hn ⟨σ, hφX⟩
      have hproper : D ⊂ matchingCore X := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨hDcore, ?_⟩
        intro heq
        apply hφD
        rw [heq] at *
        exact permSupport_subset_matchingCore hφX
      have hset :
          (Finset.univ : Finset (Finset (Fin n × Fin n))).filter
            (fun C => D ⊆ C ∧ C ⊆ X) =
          X.powerset.filter (fun C => D ⊆ C) := by
        ext C
        simp only [mem_filter, mem_univ, mem_powerset, true_and]
        tauto
      rw [hset, sum_interval_eq_matchingCore D X (matchingEulerCoefficient n) hw]
      exact hEuler D (matchingCore X) hD hcoreCovered hproper
    have hweisner := MagicSquaresSpencer.weighted_weisner D (D ∪ φ) B
      (matchingEulerCoefficient n) hA (by
        intro X hAX hXB
        have hz := hprefix X hAX hXB
        convert hz using 2
        ext C
        simp)
    have hset :
        (Finset.univ : Finset (Finset (Fin n × Fin n))).filter
          (fun C => D ⊆ C ∧ C ⊆ B ∧ C ⊔ (D ∪ φ) = B) =
        (fiberCandidates B φ).filter (fun C => D ⊆ C) := by
      ext C
      simp only [mem_filter, mem_univ, true_and, fiberCandidates,
        mem_powerset, sup_eq_union]
      constructor
      · rintro ⟨hDC, hCB, hjoin⟩
        refine ⟨⟨hCB, ?_⟩, hDC⟩
        intro e he
        have heB : e ∈ B := (mem_sdiff.mp he).1
        have hene : e ∉ φ := (mem_sdiff.mp he).2
        have heU : e ∈ C ∪ (D ∪ φ) := hjoin.symm ▸ heB
        rcases mem_union.mp heU with heC | heR
        · exact heC
        · rcases mem_union.mp heR with heD | heφ
          · exact hDC heD
          · exact False.elim (hene heφ)
      · rintro ⟨⟨hCB, hBφC⟩, hDC⟩
        refine ⟨hDC, hCB, ?_⟩
        apply Subset.antisymm
        · exact union_subset hCB (union_subset hDB hφB)
        · intro e heB
          by_cases heφ : e ∈ φ
          · exact mem_union.mpr (Or.inr (mem_union.mpr (Or.inr heφ)))
          · exact mem_union.mpr (Or.inl (hBφC (mem_sdiff.mpr ⟨heB, heφ⟩)))
    rw [← hset]
    convert hweisner using 2
    ext C
    simp

end MagicSquaresBoundary
