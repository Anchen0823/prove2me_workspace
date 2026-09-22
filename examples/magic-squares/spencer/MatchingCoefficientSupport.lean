import Definitions.Def_MagicSquaresMatchingBoundary
import examples.«magic-squares».spencer.MatchingBoundaryCriterion
import examples.«magic-squares».spencer.SupportConstants

/-!
# Public matching coefficient and support vanishing

The platform-facing finite coefficient is the same Boolean Möbius coefficient
as the Spencer-route constant `sB`.  Thus it vanishes away from matching-covered
boards once positive supports are characterized by permutation coverage.
-/

set_option autoImplicit false

namespace MagicSquaresBoundary

open Finset

theorem matchingEulerCoefficient_eq_sB (n : ℕ) (B : Finset (Fin n × Fin n)) :
    matchingEulerCoefficient n B = MagicSquaresSpencer.sB n B := by
  classical
  have hcoeff : matchingEulerCoefficient n B =
      MagicSquaresSpencer.matchingEulerCoefficient n B := by
    simp only [matchingEulerCoefficient,
      MagicSquaresSpencer.matchingEulerCoefficient]
    apply Finset.sum_congr rfl
    intro S hS
    have heq : HasPerm n (B \ S) ↔ MagicSquaresSpencer.HasPerm n (B \ S) := by
      simp only [HasPerm, MagicSquaresSpencer.HasPerm, permSupport,
        MagicSquaresSpencer.matSupport_permMatrix]
    by_cases hp : HasPerm n (B \ S)
    · rw [if_pos hp, if_pos (heq.mp hp)]
    · rw [if_neg hp, if_neg (fun h => hp (heq.mpr h))]
  calc
    matchingEulerCoefficient n B = MagicSquaresSpencer.matchingEulerCoefficient n B := hcoeff
    _ = ∑ S ∈ B.powerset, (-1 : ℚ) ^ S.card *
        (if MagicSquaresSpencer.HasPerm n (B \ S) then 1 else 0) := rfl
    _ = MagicSquaresSpencer.sB n B :=
      (MagicSquaresSpencer.sB_eq_alternating_hasPerm n B).symm

theorem matchingEulerCoefficient_eq_zero_of_not_matchingCovered (n : ℕ) (hn : 1 ≤ n)
    (B : Finset (Fin n × Fin n)) (hB : ¬ MatchingCoveredBoard n B) :
    matchingEulerCoefficient n B = 0 := by
  rw [matchingEulerCoefficient_eq_sB]
  apply MagicSquaresSpencer.sB_eq_zero_of_not_isSupport
  intro hs
  apply hB
  obtain ⟨hne, hcover⟩ :=
    (MagicSquaresSpencer.isSupport_iff_perm_coverage hn).mp hs
  refine ⟨hne, ?_⟩
  intro e he
  obtain ⟨σ, heσ, hσ⟩ := hcover e he
  refine ⟨σ, ?_, ?_⟩
  · simpa only [permSupport, MagicSquaresSpencer.matSupport_permMatrix] using heσ
  · simpa only [permSupport, MagicSquaresSpencer.matSupport_permMatrix] using hσ

end MagicSquaresBoundary
