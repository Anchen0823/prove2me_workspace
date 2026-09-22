import Definitions.Def_MagicSquaresMatchingBoundary

set_option autoImplicit false

namespace MagicSquaresBoundary
open Finset

/-- The union of all permutation supports allowed by a board. -/
noncomputable def matchingCore {n : ℕ} (B : Finset (Fin n × Fin n)) :
    Finset (Fin n × Fin n) := by
  classical
  exact B.filter fun e => ∃ σ : Equiv.Perm (Fin n),
    e ∈ permSupport σ ∧ permSupport σ ⊆ B

theorem mem_matchingCore {n : ℕ} {B : Finset (Fin n × Fin n)}
    {e : Fin n × Fin n} :
    e ∈ matchingCore B ↔ ∃ σ : Equiv.Perm (Fin n),
      e ∈ permSupport σ ∧ permSupport σ ⊆ B := by
  classical
  simp only [matchingCore, mem_filter]
  exact ⟨fun h => h.2, fun ⟨σ, he, hσ⟩ => ⟨hσ he, σ, he, hσ⟩⟩

theorem matchingCore_subset {n : ℕ} (B : Finset (Fin n × Fin n)) :
    matchingCore B ⊆ B := by
  intro e he
  obtain ⟨σ, heσ, hσ⟩ := mem_matchingCore.mp he
  exact hσ heσ

theorem permSupport_subset_matchingCore {n : ℕ} {B : Finset (Fin n × Fin n)}
    {σ : Equiv.Perm (Fin n)} (hσ : permSupport σ ⊆ B) :
    permSupport σ ⊆ matchingCore B := by
  exact fun _ he => mem_matchingCore.mpr ⟨σ, he, hσ⟩

theorem matchingCore_mono {n : ℕ} {B C : Finset (Fin n × Fin n)} (h : B ⊆ C) :
    matchingCore B ⊆ matchingCore C := by
  intro e he
  obtain ⟨σ, heσ, hσ⟩ := mem_matchingCore.mp he
  exact mem_matchingCore.mpr ⟨σ, heσ, hσ.trans h⟩

theorem matchingCovered_subset_core_iff {n : ℕ}
    {D B : Finset (Fin n × Fin n)} (hD : MatchingCoveredBoard n D) :
    D ⊆ matchingCore B ↔ D ⊆ B := by
  constructor
  · exact fun h => h.trans (matchingCore_subset B)
  · intro h e he
    obtain ⟨σ, heσ, hσ⟩ := hD.2 e he
    exact mem_matchingCore.mpr ⟨σ, heσ, hσ.trans h⟩

theorem matchingCore_eq_self {n : ℕ} {B : Finset (Fin n × Fin n)}
    (hB : MatchingCoveredBoard n B) : matchingCore B = B :=
  Subset.antisymm (matchingCore_subset B)
    ((matchingCovered_subset_core_iff hB).mpr Subset.rfl)

theorem matchingCore_matchingCovered {n : ℕ} (hn : 1 ≤ n)
    {B : Finset (Fin n × Fin n)} (hB : HasPerm n B) :
    MatchingCoveredBoard n (matchingCore B) := by
  classical
  obtain ⟨σ, hσ⟩ := hB
  constructor
  · let i : Fin n := ⟨0, hn⟩
    exact ⟨(i, σ i), permSupport_subset_matchingCore hσ
      (by simp [permSupport])⟩
  · intro e he
    obtain ⟨τ, heτ, hτ⟩ := mem_matchingCore.mp he
    exact ⟨τ, heτ, permSupport_subset_matchingCore hτ⟩

theorem matchingCovered_union {n : ℕ} {B C : Finset (Fin n × Fin n)}
    (hB : MatchingCoveredBoard n B) (hC : MatchingCoveredBoard n C) :
    MatchingCoveredBoard n (B ∪ C) := by
  classical
  constructor
  · exact hB.1.mono subset_union_left
  · intro e he
    rcases mem_union.mp he with he | he
    · obtain ⟨σ, heσ, hσ⟩ := hB.2 e he
      exact ⟨σ, heσ, hσ.trans subset_union_left⟩
    · obtain ⟨σ, heσ, hσ⟩ := hC.2 e he
      exact ⟨σ, heσ, hσ.trans subset_union_right⟩

theorem matchingCore_idempotent {n : ℕ} (B : Finset (Fin n × Fin n)) :
    matchingCore (matchingCore B) = matchingCore B := by
  apply Subset.antisymm (matchingCore_subset _)
  intro e he
  obtain ⟨σ, heσ, hσ⟩ := mem_matchingCore.mp he
  exact mem_matchingCore.mpr ⟨σ, heσ, permSupport_subset_matchingCore hσ⟩

theorem permSupport_matchingCovered {n : ℕ} (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin n)) : MatchingCoveredBoard n (permSupport σ) := by
  classical
  constructor
  · let i : Fin n := ⟨0, hn⟩
    exact ⟨(i, σ i), by simp [permSupport]⟩
  · exact fun _ he => ⟨σ, he, Subset.rfl⟩

/-- Weights supported on matching-covered boards see only the matching core.
This transfers interval Euler identities from realizable to arbitrary boards. -/
theorem sum_interval_eq_matchingCore {n : ℕ}
    (D B : Finset (Fin n × Fin n)) (w : Finset (Fin n × Fin n) → ℚ)
    (hw : ∀ C, ¬ MatchingCoveredBoard n C → w C = 0) :
    (∑ C ∈ B.powerset.filter (fun C => D ⊆ C), w C) =
      ∑ C ∈ (matchingCore B).powerset.filter (fun C => D ⊆ C), w C := by
  classical
  symm
  apply Finset.sum_subset
  · intro C hC
    simp only [mem_filter, mem_powerset] at hC ⊢
    exact ⟨hC.1.trans (matchingCore_subset B), hC.2⟩
  · intro C hC hmiss
    apply hw C
    intro hcovered
    apply hmiss
    simp only [mem_filter, mem_powerset] at hC ⊢
    exact ⟨(matchingCovered_subset_core_iff hcovered).mpr hC.1, hC.2⟩

end MagicSquaresBoundary
