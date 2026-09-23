import examples.«magic-squares».spencer.MatchingIntervalEuler

set_option autoImplicit false



/-! ## Adapter from the public finite predicate -/

theorem matching_boundary_adapter (n : ℕ)
    (h : MagicSquaresBoundary.MatchingBoundaryCriterion n) :
    MagicSquaresSpencer.MatchingBoundaryCriterion n := by
  have hcoeff (B : Finset (Fin n × Fin n)) :
      MagicSquaresBoundary.matchingEulerCoefficient n B =
        MagicSquaresSpencer.matchingEulerCoefficient n B := by
    classical
    simp only [MagicSquaresBoundary.matchingEulerCoefficient,
      MagicSquaresSpencer.matchingEulerCoefficient]
    apply Finset.sum_congr rfl
    intro S hS
    have heq : MagicSquaresBoundary.HasPerm n (B \ S) ↔
        MagicSquaresSpencer.HasPerm n (B \ S) := by
      simp only [MagicSquaresBoundary.HasPerm, MagicSquaresSpencer.HasPerm,
        MagicSquaresBoundary.permSupport, MagicSquaresSpencer.matSupport_permMatrix]
    by_cases hp : MagicSquaresBoundary.HasPerm n (B \ S)
    · rw [if_pos hp, if_pos (heq.mp hp)]
    · rw [if_neg hp, if_neg (fun h => hp (heq.mpr h))]
  have hcand (B φ : Finset (Fin n × Fin n)) :
      MagicSquaresBoundary.fiberCandidates B φ =
        MagicSquaresSpencer.fiberCandidates B φ := by
    classical
    ext C
    simp [MagicSquaresBoundary.fiberCandidates,
      MagicSquaresSpencer.fiberCandidates]
  simpa only [MagicSquaresBoundary.MatchingBoundaryCriterion,
    MagicSquaresBoundary.MatchingCoveredBoard,
    MagicSquaresBoundary.permSupport,
    MagicSquaresSpencer.MatchingBoundaryCriterion,
    MagicSquaresSpencer.MatchingCoveredBoard,
    MagicSquaresSpencer.matSupport_permMatrix, hcoeff, hcand] using h


namespace MagicSquares

/-- The complete Mission V root, using the proved finite matching boundary. -/
theorem semi_magic_polynomial_completed (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : Polynomial ℚ,
      p.natDegree = (n - 1) ^ 2 ∧
        (∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)) ∧
          (∀ t : ℤ, p.eval (((-(n : ℤ) - t : ℤ) : ℚ)) =
            (-1 : ℚ) ^ (n - 1) * p.eval (t : ℚ)) ∧
          (∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) - 1 → p.eval (-(k : ℚ)) = 0) := by
  apply MagicSquaresSpencer.semiMagic_root_of_finiteBoundaryEuler n hn
  apply (MagicSquaresSpencer.matchingBoundaryCriterion_iff_finiteBoundaryEuler n hn).mp
  exact matching_boundary_adapter n (MagicSquaresBoundary.matchingBoundaryCriterion_proved n hn)

end MagicSquares
