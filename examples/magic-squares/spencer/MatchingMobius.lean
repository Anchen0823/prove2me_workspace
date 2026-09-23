import examples.«magic-squares».spencer.MatchingCoefficientSupport
import examples.«magic-squares».spencer.MatchingCore
import examples.«magic-squares».spencer.SupportedSubtypeSum
import examples.«magic-squares».spencer.FiniteMobiusWeights

set_option autoImplicit false

namespace MagicSquaresBoundary

open Finset
attribute [local instance] Classical.propDecidable

/-- The support poset includes the empty board, corresponding to the zero face. -/
abbrev MatchingBoard (n : ℕ) :=
  {B : Finset (Fin n × Fin n) // B = ∅ ∨ MatchingCoveredBoard n B}

instance matchingBoardOrderBot (n : ℕ) : OrderBot (MatchingBoard n) where
  bot := ⟨∅, Or.inl rfl⟩
  bot_le B := Finset.empty_subset B.val

theorem matchingBoard_eq_bot_iff (n : ℕ) (B : MatchingBoard n) :
    B = ⊥ ↔ B.val = ∅ := by
  constructor
  · rintro rfl
    rfl
  · exact fun h => Subtype.ext h

theorem matchingEulerCoefficient_empty (n : ℕ) (hn : 1 ≤ n) :
    matchingEulerCoefficient n ∅ = 0 := by
  apply matchingEulerCoefficient_eq_zero_of_not_matchingCovered n hn
  simp [MatchingCoveredBoard]

theorem matchingEulerCoefficient_prefix (n : ℕ) (B : Finset (Fin n × Fin n)) :
    (∑ C ∈ B.powerset, matchingEulerCoefficient n C) =
      if HasPerm n B then 1 else 0 := by
  classical
  simp_rw [matchingEulerCoefficient_eq_sB]
  rw [MagicSquaresSpencer.sum_sB_powerset_eq_indicator]
  have h : HasPerm n B ↔ MagicSquaresSpencer.HasPerm n B := by
    simp only [HasPerm, MagicSquaresSpencer.HasPerm, permSupport,
      MagicSquaresSpencer.matSupport_permMatrix]
  simp only [h]

/-- The bottom coefficient must be restored before it is a Mobius weight. -/
noncomputable def matchingMobiusWeight (n : ℕ) (B : MatchingBoard n) : ℚ :=
  if B.val = ∅ then 1 else -matchingEulerCoefficient n B.val

theorem matchingMobiusWeight_eq_delta_sub (n : ℕ) (hn : 1 ≤ n)
    (B : MatchingBoard n) :
    matchingMobiusWeight n B =
      (if B = ⊥ then 1 else 0) - matchingEulerCoefficient n B.val := by
  simp only [matchingBoard_eq_bot_iff]
  by_cases h : B.val = ∅
  · simp [matchingMobiusWeight, h, matchingEulerCoefficient_empty n hn]
  · simp [matchingMobiusWeight, h]

theorem sum_coefficient_matchingBoard_prefix (n : ℕ) (hn : 1 ≤ n)
    (B : MatchingBoard n) :
    (∑ C ∈ (Finset.univ : Finset (MatchingBoard n)).filter (fun C => C ≤ B),
      matchingEulerCoefficient n C.val) = if B = ⊥ then 0 else 1 := by
  classical
  have ht := FiniteSupport.sum_subtype_filter_eq_sum_filter_of_zero_outside
    (fun C : Finset (Fin n × Fin n) => C = ∅ ∨ MatchingCoveredBoard n C)
    (fun C => C ⊆ B.val) (matchingEulerCoefficient n)
    (fun C hC => matchingEulerCoefficient_eq_zero_of_not_matchingCovered n hn C
      (fun hc => hC (Or.inr hc)))
  have hset : (Finset.univ : Finset (Finset (Fin n × Fin n))).filter
      (fun C => C ⊆ B.val) = B.val.powerset := by
    ext C
    simp
  change (∑ C ∈ (Finset.univ : Finset (MatchingBoard n)).filter
    (fun C => C.val ⊆ B.val), matchingEulerCoefficient n C.val) = _
  rw [ht, hset, matchingEulerCoefficient_prefix]
  by_cases hB : B = ⊥
  · subst B
    have hno : ¬ HasPerm n (∅ : Finset (Fin n × Fin n)) := by
      rintro ⟨σ, hσ⟩
      have hmem : ((⟨0, hn⟩ : Fin n), σ ⟨0, hn⟩) ∈ permSupport σ := by
        simp [permSupport]
      exact Finset.notMem_empty _ (hσ hmem)
    change (if HasPerm n ∅ then (1 : ℚ) else 0) = if (⊥ : MatchingBoard n) = ⊥ then 0 else 1
    simp [hno]
  · have hcov : MatchingCoveredBoard n B.val := B.property.resolve_left
        (fun h => hB ((matchingBoard_eq_bot_iff n B).mpr h))
    obtain ⟨e, he⟩ := hcov.1
    obtain ⟨σ, -, hσ⟩ := hcov.2 e he
    simp [hB, show HasPerm n B.val from ⟨σ, hσ⟩]

theorem matchingMobiusWeight_prefix (n : ℕ) (hn : 1 ≤ n)
    (B : MatchingBoard n) :
    (∑ C ∈ (Finset.univ : Finset (MatchingBoard n)).filter (fun C => C ≤ B),
      matchingMobiusWeight n C) = if B = ⊥ then 1 else 0 := by
  classical
  simp_rw [matchingMobiusWeight_eq_delta_sub n hn]
  rw [Finset.sum_sub_distrib, sum_coefficient_matchingBoard_prefix n hn]
  have hd : (∑ C ∈ (Finset.univ : Finset (MatchingBoard n)).filter (fun C => C ≤ B),
      (if C = ⊥ then (1 : ℚ) else 0)) = 1 := by
    simp
  rw [hd]
  split_ifs <;> norm_num

theorem matchingMobiusWeight_eq_mu (n : ℕ) (hn : 1 ≤ n) (B : MatchingBoard n) :
    matchingMobiusWeight n B = IncidenceAlgebra.mu ℚ ⊥ B := by
  classical
  refine MagicSquaresGeometry.weights_eq_mobius_from_bottom
    (matchingMobiusWeight n) (fun b => ?_) B
  convert matchingMobiusWeight_prefix n hn b using 1
  apply Finset.sum_congr
  · ext C
    simp
  · intro C hC
    rfl

/-- The finite matching coefficient is the negative bottom Mobius number. -/
theorem matchingEulerCoefficient_eq_neg_mu (n : ℕ) (hn : 1 ≤ n)
    (B : MatchingBoard n) (hB : B ≠ ⊥) :
    matchingEulerCoefficient n B.val = -IncidenceAlgebra.mu ℚ ⊥ B := by
  have h := matchingMobiusWeight_eq_mu n hn B
  have hne := fun he => hB ((matchingBoard_eq_bot_iff n B).mpr he)
  simp only [matchingMobiusWeight, if_neg hne] at h
  linarith

/-- Transfer the actual interval coefficient sum, including its minus sign,
to the support-poset Mobius weights. This does not assume an Euler relation. -/
theorem matching_interval_sum_eq_neg_mu_sum (n : ℕ) (hn : 1 ≤ n)
    (D B : MatchingBoard n) (hD : D ≠ ⊥) :
    (∑ C ∈ B.val.powerset.filter (fun C => D.val ⊆ C), matchingEulerCoefficient n C) =
      -(∑ C ∈ (Finset.univ : Finset (MatchingBoard n)).filter
        (fun C => D ≤ C ∧ C ≤ B), IncidenceAlgebra.mu ℚ ⊥ C) := by
  classical
  have ht := FiniteSupport.sum_subtype_filter_eq_sum_filter_of_zero_outside
    (fun C : Finset (Fin n × Fin n) => C = ∅ ∨ MatchingCoveredBoard n C)
    (fun C => D.val ⊆ C ∧ C ⊆ B.val) (matchingEulerCoefficient n)
    (fun C hC => matchingEulerCoefficient_eq_zero_of_not_matchingCovered n hn C
      (fun hc => hC (Or.inr hc)))
  have hset : (Finset.univ : Finset (Finset (Fin n × Fin n))).filter
      (fun C => D.val ⊆ C ∧ C ⊆ B.val) =
      B.val.powerset.filter (fun C => D.val ⊆ C) := by
    ext C
    simp [and_comm]
  rw [hset] at ht
  rw [← ht, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro C hC
  have hDC : D ≤ C := (Finset.mem_filter.mp hC).2.1
  apply matchingEulerCoefficient_eq_neg_mu n hn C
  intro hC0
  exact hD (le_antisymm (hC0 ▸ hDC) bot_le)

end MagicSquaresBoundary
