import Mathlib

/-! A finite matching criterion for the boundary reciprocity reduction. -/

namespace MagicSquaresBoundary

open Finset

noncomputable def permSupport {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Finset (Fin n × Fin n) :=
  Finset.univ.image fun i => (i, σ i)

def HasPerm (n : ℕ) (B : Finset (Fin n × Fin n)) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), permSupport σ ⊆ B

def MatchingCoveredBoard (n : ℕ) (B : Finset (Fin n × Fin n)) : Prop :=
  B.Nonempty ∧ ∀ e ∈ B, ∃ σ : Equiv.Perm (Fin n),
    e ∈ permSupport σ ∧ permSupport σ ⊆ B

noncomputable def matchingEulerCoefficient (n : ℕ)
    (B : Finset (Fin n × Fin n)) : ℚ := by
  classical
  exact ∑ S ∈ B.powerset, (-1 : ℚ) ^ S.card *
    (if HasPerm n (B \ S) then 1 else 0)

noncomputable def fiberCandidates {n : ℕ}
    (B φ : Finset (Fin n × Fin n)) :
    Finset (Finset (Fin n × Fin n)) := by
  classical
  exact B.powerset.filter fun C => B \ φ ⊆ C

def MatchingBoundaryCriterion (n : ℕ) : Prop :=
  ∀ B : Finset (Fin n × Fin n), MatchingCoveredBoard n B →
    ∀ σ : Equiv.Perm (Fin n), permSupport σ ⊆ B →
      ∀ D : Finset (Fin n × Fin n), MatchingCoveredBoard n D → D ⊆ B →
        (∑ C ∈ (fiberCandidates B (permSupport σ)).filter
          (fun C => D ⊆ C), matchingEulerCoefficient n C) =
          if permSupport σ ⊆ D then matchingEulerCoefficient n B else 0

end MagicSquaresBoundary
