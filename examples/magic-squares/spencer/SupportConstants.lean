import examples.«magic-squares».spencer.ClosedEvaluation
import examples.«magic-squares».spencer.SupportPartition
import examples.«magic-squares».spencer.SupportExactIE
import examples.«magic-squares».spencer.SupportCoverage

set_option autoImplicit false

namespace MagicSquaresSpencer

open Finset Polynomial
attribute [local instance] Classical.propDecidable

/-- Closed-support counting is the sum of exact-support counting polynomials.
This identity is extended from positive integer line sums, so it also holds at zero. -/
theorem closedPoly_eq_sum_qB (n : ℕ) (B : Finset (Fin n × Fin n)) :
    closedPoly n B = ∑ C ∈ B.powerset, (qB n C).comp (X - 1) := by
  classical
  apply sub_eq_zero.mp
  apply poly_eq_zero_of_pos_eval_eq_zero
  intro t ht
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  simp only [Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_comp,
    Polynomial.eval_X, Polynomial.eval_one]
  have hshift : ((r + 1 : ℕ) : ℚ) - 1 = (r : ℚ) := by push_cast; ring
  rw [hshift, closedPoly_eval_pos]
  simp_rw [qB_eval]
  exact sub_eq_zero.mpr (card_closedFiber_eq_sum_matFiber_rat n (r + 1) B)

/-- At zero, a closed counting polynomial detects whether the board contains a
permutation. This convention includes inadmissible boards, whose polynomial is zero. -/
theorem closedPoly_eval_zero_indicator (n : ℕ) (B : Finset (Fin n × Fin n)) :
    (closedPoly n B).eval 0 = if HasPerm n B then 1 else 0 := by
  classical
  by_cases h : HasPerm n B
  · rw [if_pos h, closedPoly_eval_zero h]
  · simp [closedPoly, h]

/-- The constant terms of exact-support polynomials sum to the perfect-matching
indicator on every board, not just the complete board. -/
theorem sum_sB_powerset_eq_indicator (n : ℕ) (B : Finset (Fin n × Fin n)) :
    ∑ C ∈ B.powerset, sB n C = if HasPerm n B then 1 else 0 := by
  classical
  have h := congrArg (fun p : Polynomial ℚ => p.eval 0) (closedPoly_eq_sum_qB n B)
  simpa only [closedPoly_eval_zero_indicator, Polynomial.eval_finsetSum,
    Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_one, zero_sub, sB] using h.symm

/-- Inclusion-exclusion identifies the entire exact-support polynomial, not only
its positive integer values. -/
theorem qB_comp_eq_alternating_closedPoly (n : ℕ) (B : Finset (Fin n × Fin n)) :
    (qB n B).comp (X - 1) =
      ∑ S ∈ B.powerset, C ((-1 : ℚ) ^ S.card) * closedPoly n (B \ S) := by
  classical
  apply sub_eq_zero.mp
  apply poly_eq_zero_of_pos_eval_eq_zero
  intro t ht
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
  have hshift : ((r + 1 : ℕ) : ℚ) - 1 = (r : ℚ) := by push_cast; ring
  rw [hshift, qB_eval]
  simp_rw [closedPoly_eval_pos]
  apply sub_eq_zero.mpr
  simpa only [gB, matFiber_eq_filter_matBoxLine, closedFiber] using
    card_filter_eq_support_eq_sum_subset_sdiff (matBoxLine n (r + 1)) matSupport B

/-- The exact-support constant is the Boolean Möbius transform of the indicator
that a board contains a perfect matching. This is unconditional; identifying its
value with a dimension sign is a separate Euler-characteristic problem. -/
theorem sB_eq_alternating_hasPerm (n : ℕ) (B : Finset (Fin n × Fin n)) :
    sB n B = ∑ S ∈ B.powerset,
      (-1 : ℚ) ^ S.card * (if HasPerm n (B \ S) then 1 else 0) := by
  classical
  have h := congrArg (fun p : Polynomial ℚ => p.eval 0)
    (qB_comp_eq_alternating_closedPoly n B)
  simpa only [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_one, zero_sub, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, closedPoly_eval_zero_indicator, sB] using h

/-- An exact finite formulation of the old support-sign gap. This equivalence
does not claim either side, or full negative-argument reciprocity. -/
theorem reciprocityAtNegOne_iff_matching_euler (n : ℕ) :
    ReciprocityAtNegOne n ↔
      ∀ B : Finset (Fin n × Fin n), IsSupport n B →
        (∑ S ∈ B.powerset, (-1 : ℚ) ^ S.card *
          (if HasPerm n (B \ S) then 1 else 0)) = (-1 : ℚ) ^ rankB B := by
  simp only [ReciprocityAtNegOne, sB_eq_alternating_hasPerm]

/-- The alternating matching sum vanishes on boards that cannot occur as the
exact support of a positive-level semi-magic square. -/
theorem alternating_hasPerm_eq_zero_of_not_isSupport {n : ℕ}
    {B : Finset (Fin n × Fin n)} (h : ¬ IsSupport n B) :
    (∑ S ∈ B.powerset, (-1 : ℚ) ^ S.card *
      (if HasPerm n (B \ S) then 1 else 0)) = 0 := by
  rw [← sB_eq_alternating_hasPerm]
  exact sB_eq_zero_of_not_isSupport h

/-- An edge that lies in no contained perfect matching forces cancellation in
the finite alternating sum. -/
theorem alternating_hasPerm_eq_zero_of_uncovered_cell {n : ℕ}
    {B : Finset (Fin n × Fin n)} {e : Fin n × Fin n} (he : e ∈ B)
    (hmiss : ∀ σ : Equiv.Perm (Fin n), matSupport (permMatrix σ) ⊆ B →
      e ∉ matSupport (permMatrix σ)) :
    (∑ S ∈ B.powerset, (-1 : ℚ) ^ S.card *
      (if HasPerm n (B \ S) then 1 else 0)) = 0 := by
  apply alternating_hasPerm_eq_zero_of_not_isSupport
  intro hB
  obtain ⟨σ, heσ, hσ⟩ := exists_perm_support_covering_cell hB he
  exact hmiss σ hσ heσ

end MagicSquaresSpencer
