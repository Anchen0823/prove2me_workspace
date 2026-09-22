import examples.«magic-squares».spencer.ReciprocityFromBoundary

set_option autoImplicit false

namespace MagicSquaresSpencer
open Finset Polynomial
attribute [local instance] Classical.propDecidable

/-- A finite Boolean Möbius coefficient; no counting polynomial occurs here. -/
noncomputable def matchingEulerCoefficient (n : ℕ) (B : Finset (Fin n × Fin n)) : ℚ :=
  ∑ S ∈ B.powerset, (-1 : ℚ) ^ S.card * (if HasPerm n (B \ S) then 1 else 0)

/-- Realizable support described solely by a finite family of permutations. -/
def MatchingCoveredBoard (n : ℕ) (B : Finset (Fin n × Fin n)) : Prop :=
  B.Nonempty ∧ ∀ e ∈ B, ∃ σ : Equiv.Perm (Fin n),
    e ∈ matSupport (permMatrix σ) ∧ matSupport (permMatrix σ) ⊆ B

/-- The remaining combinatorial hypothesis, with both coefficients and guards
expanded into finite matching predicates. This definition asserts no proof. -/
def MatchingBoundaryCriterion (n : ℕ) : Prop :=
  ∀ B : Finset (Fin n × Fin n), MatchingCoveredBoard n B →
    ∀ σ : Equiv.Perm (Fin n), matSupport (permMatrix σ) ⊆ B →
      ∀ D : Finset (Fin n × Fin n), MatchingCoveredBoard n D → D ⊆ B →
        (∑ C ∈ (fiberCandidates B (matSupport (permMatrix σ))).filter
          (fun C => D ⊆ C), matchingEulerCoefficient n C) =
          if matSupport (permMatrix σ) ⊆ D then matchingEulerCoefficient n B else 0

theorem matchingBoundaryCriterion_iff_finiteBoundaryEuler (n : ℕ) (hn : 1 ≤ n) :
    MatchingBoundaryCriterion n ↔ FiniteBoundaryEuler n := by
  simp only [MatchingBoundaryCriterion, FiniteBoundaryEuler, MatchingCoveredBoard,
    matchingEulerCoefficient, isSupport_iff_perm_coverage hn, sB_eq_alternating_hasPerm]

/-- The exact reciprocity conclusion follows from a purely finite matching
criterion. The criterion itself remains an explicit, unproved hypothesis. -/
theorem semiMagic_reciprocity_of_matchingBoundaryCriterion (n : ℕ) (hn : 1 ≤ n)
    (p : Polynomial ℚ)
    (hp : ∀ t : ℕ, p.eval (t : ℚ) = (MagicSquares.semiMagicCount n t : ℚ))
    (he : MatchingBoundaryCriterion n) :
    ∀ t : ℤ, p.eval (((-(n : ℤ) - t : ℤ) : ℚ)) =
      (-1 : ℚ) ^ (n - 1) * p.eval (t : ℚ) :=
  semiMagic_reciprocity_of_finiteBoundaryEuler n hn p hp
    ((matchingBoundaryCriterion_iff_finiteBoundaryEuler n hn).mp he)

end MagicSquaresSpencer
