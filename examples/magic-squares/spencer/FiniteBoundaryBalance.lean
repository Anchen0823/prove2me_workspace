import examples.«magic-squares».spencer.ReciprocityPropagation

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace MagicSquaresSpencer

open Finset Polynomial

attribute [local instance] Classical.propDecidable

/-- A finite Euler identity on every support occurring in a closed fibre. -/
def FiniteBoundaryEuler (n : ℕ) : Prop :=
  ∀ B : Finset (Fin n × Fin n), IsSupport n B →
    ∀ σ : Equiv.Perm (Fin n), matSupport (permMatrix σ) ⊆ B →
      ∀ D : Finset (Fin n × Fin n), IsSupport n D → D ⊆ B →
        (∑ C ∈ (fiberCandidates B (matSupport (permMatrix σ))).filter
          (fun C => D ⊆ C), sB n C) =
          if matSupport (permMatrix σ) ⊆ D then sB n B else 0

theorem finiteBoundaryEuler_implies_boundaryBalance (n : ℕ)
    (he : FiniteBoundaryEuler n) : BoundaryBalance n := by
  classical
  intro B hB σ hσ x
  let φ := matSupport (permMatrix σ)
  let F := fiberCandidates B φ
  let P : Polynomial ℚ := ∑ D ∈ F, Polynomial.C (sB n D) * closedPoly n D
  let Q : Polynomial ℚ := C (sB n B) * (closedPoly n B).comp (X - 1)
  have hp : P = Q := by
    apply sub_eq_zero.mp
    apply poly_eq_zero_of_pos_eval_eq_zero
    intro u hu
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : u ≠ 0)
    have hsum :
        (∑ C ∈ F, sB n C * ((closedFiber n (t + 1) C).card : ℚ)) =
        sB n B * ((closedFiber n t B).card : ℚ) := by
      let A := closedFiber n (t + 1) B
      have hswap :
          (∑ C ∈ F, sB n C * ((closedFiber n (t + 1) C).card : ℚ)) =
          ∑ M ∈ A, ∑ C ∈ F.filter (fun C => matSupport M ⊆ C), sB n C := by
        have hinner (C : Finset (Fin n × Fin n)) (hC : C ∈ F) :
            ((closedFiber n (t + 1) C).card : ℚ) =
              ∑ M ∈ A, if matSupport M ⊆ C then (1 : ℚ) else 0 := by
          have hCB : C ⊆ B := (mem_fiberCandidates.mp hC).1
          have hset : closedFiber n (t + 1) C =
              A.filter (fun M => matSupport M ⊆ C) := by
            ext M
            simp only [mem_closedFiber, Finset.mem_filter, A]
            exact ⟨fun h => ⟨⟨h.1, h.2.trans hCB⟩, h.2⟩,
              fun h => ⟨h.1.1, h.2⟩⟩
          rw [hset]
          simp
        rw [Finset.sum_congr rfl (fun C hC => by rw [hinner C hC])]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro M hM
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite,
          Finset.sum_const_zero, add_zero]
      rw [hswap]
      have hterms (M : Matrix (Fin n) (Fin n) ℕ) (hM : M ∈ A) :
          (∑ C ∈ F.filter (fun C => matSupport M ⊆ C), sB n C) =
          if φ ⊆ matSupport M then sB n B else 0 := by
        have hD : IsSupport n (matSupport M) := by
          refine ⟨t + 1, by omega, M, ?_⟩
          rw [matFiber_eq_filter_matBoxLine]
          exact Finset.mem_filter.mpr ⟨(mem_closedFiber.mp hM).1, rfl⟩
        have hsub : matSupport M ⊆ B := (mem_closedFiber.mp hM).2
        exact he B hB σ hσ (matSupport M) hD hsub
      rw [Finset.sum_congr rfl (fun M hM => hterms M hM)]
      have hc := card_closedFiber_filter_permSupport n t B σ hσ
      rw [← hc]
      simp [A, φ, Finset.sum_ite, mul_comm]
    simp only [Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_one, P, Q]
    have hshift : (((t + 1 : ℕ) : ℚ) - 1) = (t : ℚ) := by push_cast; ring
    rw [hshift]
    simp_rw [closedPoly_eval_pos]
    rw [closedPoly_eval_of_hasPerm ⟨σ, hσ⟩]
    exact sub_eq_zero.mpr hsum
  have hv := congrArg (fun p : Polynomial ℚ => p.eval x) hp
  simpa only [P, Q, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_one, F, φ] using hv

end MagicSquaresSpencer
