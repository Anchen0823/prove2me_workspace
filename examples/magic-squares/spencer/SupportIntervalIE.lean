import examples.«magic-squares».spencer.MatchingCoefficientSupport
import examples.«magic-squares».spencer.MatchingDeletion

set_option autoImplicit false

namespace MagicSquaresSpencer

open Finset
attribute [local instance] Classical.propDecidable

/-- Inclusion-exclusion of the lower endpoint of a Boolean interval. -/
theorem sum_interval_of_powerset_sums {α : Type*} [DecidableEq α]
    (D B : Finset α) (g f : Finset α → ℚ)
    (hf : ∀ A : Finset α, f A = ∑ C ∈ A.powerset, g C) :
    (∑ C ∈ B.powerset.filter (fun C => D ⊆ C), g C) =
      ∑ S ∈ D.powerset, (-1 : ℚ) ^ S.card * f (B \ S) := by
  classical
  have halt (T : Finset α) :
      (∑ S ∈ T.powerset, (-1 : ℚ) ^ S.card) =
        if T = ∅ then 1 else 0 := by
    exact_mod_cast (Finset.sum_powerset_neg_one_pow_card (x := T))
  have hsub (S : Finset α) (hSD : S ⊆ D) :
      (B \ S).powerset = B.powerset.filter (fun C => Disjoint C S) := by
    ext C
    simp only [mem_powerset, mem_filter]
    constructor
    · intro h
      exact ⟨h.trans sdiff_subset, disjoint_left.mpr
          (fun e heC heS => (mem_sdiff.mp (h heC)).2 heS)⟩
    · rintro ⟨hCB, hdis⟩
      intro e heC
      exact mem_sdiff.mpr ⟨hCB heC, (disjoint_left.mp hdis) heC⟩
  calc
    (∑ C ∈ B.powerset.filter (fun C => D ⊆ C), g C) =
        ∑ C ∈ B.powerset, g C *
          (∑ S ∈ (D \ C).powerset, (-1 : ℚ) ^ S.card) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro C hCB
      rw [halt]
      by_cases hDC : D ⊆ C
      · simp [hDC, Finset.sdiff_eq_empty_iff_subset.mpr hDC]
      · have hn : D \ C ≠ ∅ := by simpa [Finset.sdiff_eq_empty_iff_subset] using hDC
        simp [hDC, hn]
    _ = ∑ S ∈ D.powerset, (-1 : ℚ) ^ S.card * f (B \ S) := by
      simp_rw [hf]
      apply Eq.symm
      calc
        (∑ S ∈ D.powerset, (-1 : ℚ) ^ S.card *
            ∑ C ∈ (B \ S).powerset, g C) =
            ∑ S ∈ D.powerset, ∑ C ∈ B.powerset,
              if Disjoint C S then (-1 : ℚ) ^ S.card * g C else 0 := by
          apply Finset.sum_congr rfl
          intro S hSD
          rw [hsub S (mem_powerset.mp hSD), Finset.sum_filter]
          simp_rw [mul_sum]
          simp only [mul_ite, mul_zero]
        _ = ∑ C ∈ B.powerset, ∑ S ∈ D.powerset,
              if Disjoint C S then (-1 : ℚ) ^ S.card * g C else 0 :=
            Finset.sum_comm
        _ = ∑ C ∈ B.powerset, g C *
              (∑ S ∈ (D \ C).powerset, (-1 : ℚ) ^ S.card) := by
          apply Finset.sum_congr rfl
          intro C hCB
          have hset : D.powerset.filter (fun S => Disjoint C S) =
              (D \ C).powerset := by
            ext S
            simp only [mem_filter, mem_powerset]
            constructor
            · rintro ⟨hSD, hdis⟩
              intro e heS
              exact mem_sdiff.mpr ⟨hSD heS, (disjoint_left.mp hdis.symm) heS⟩
            · intro hS
              exact ⟨hS.trans sdiff_subset, disjoint_left.mpr
                (fun e heC heS => (mem_sdiff.mp (hS heS)).2 heC)⟩
          rw [← hset, Finset.sum_filter]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S hSD
          by_cases h : Disjoint C S <;> simp [h, mul_comm]

end MagicSquaresSpencer

namespace MagicSquaresBoundary

open Finset
attribute [local instance] Classical.propDecidable

/-- The interval of coefficients is exactly an alternating matching-deletion sum. -/
theorem matching_interval_sum_eq_deletion_sum (n : ℕ)
    (D B : Finset (Fin n × Fin n)) :
    (∑ C ∈ B.powerset.filter (fun C => D ⊆ C), matchingEulerCoefficient n C) =
      ∑ S ∈ D.powerset, (-1 : ℚ) ^ S.card *
        (if HasPerm n (B \ S) then 1 else 0) := by
  classical
  apply MagicSquaresSpencer.sum_interval_of_powerset_sums D B
    (matchingEulerCoefficient n) (fun A => if HasPerm n A then 1 else 0)
  intro A
  have hp : HasPerm n A ↔ MagicSquaresSpencer.HasPerm n A := by
    simp only [HasPerm, MagicSquaresSpencer.HasPerm, permSupport,
      MagicSquaresSpencer.matSupport_permMatrix]
  rw [show (if HasPerm n A then (1 : ℚ) else 0) =
      if MagicSquaresSpencer.HasPerm n A then 1 else 0 from by simp only [hp]]
  rw [← MagicSquaresSpencer.sum_sB_powerset_eq_indicator n A]
  exact Finset.sum_congr rfl (fun C _ => matchingEulerCoefficient_eq_sB n C |>.symm)

/-- Every interval with a nonempty lower board and a matching outside it cancels. -/
theorem matching_interval_sum_eq_zero_of_complement_matching (n : ℕ)
    (D B : Finset (Fin n × Fin n)) (hD : D.Nonempty)
    (hmatch : HasPerm n (B \ D)) :
    (∑ C ∈ B.powerset.filter (fun C => D ⊆ C), matchingEulerCoefficient n C) = 0 := by
  rw [matching_interval_sum_eq_deletion_sum]
  exact deletion_sum_eq_zero_of_complement_matching n D B hD hmatch

end MagicSquaresBoundary
