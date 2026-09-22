import examples.«magic-squares».spencer.SupportConstants
import examples.«magic-squares».spencer.PolynomialDifference
import examples.«magic-squares».spencer.FirstNegativeValue

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace MagicSquaresSpencer
open Finset Polynomial

/-- A finite-boundary balance, expressed as an identity of counting polynomials.
This is a hypothesis, not an asserted Euler theorem. -/
def BoundaryBalance (n : ℕ) : Prop :=
  ∀ B : Finset (Fin n × Fin n), IsSupport n B →
    ∀ σ : Equiv.Perm (Fin n), matSupport (permMatrix σ) ⊆ B →
      ∀ x : ℚ,
        (∑ C ∈ fiberCandidates B (matSupport (permMatrix σ)),
          sB n C * (closedPoly n C).eval x) =
        sB n B * (closedPoly n B).eval (x - 1)

theorem qB_rec_perm (n : ℕ) (B : Finset (Fin n × Fin n))
    (σ : Equiv.Perm (Fin n)) (hσ : matSupport (permMatrix σ) ⊆ B) (x : ℚ) :
    (qB n B).eval (x + 1) - (qB n B).eval x =
      ∑ C ∈ nbSupp B (matSupport (permMatrix σ)), (qB n C).eval x := by
  classical
  have hp : (qB n B).comp (X + 1) - qB n B -
      ∑ C ∈ nbSupp B (matSupport (permMatrix σ)), qB n C = 0 := by
    apply poly_eq_zero_of_nat_eval_eq_zero
    intro t
    simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_finsetSum]
    have hc : (t : ℚ) + 1 = ((t + 1 : ℕ) : ℚ) := by simp
    rw [hc, qB_eval, qB_eval]
    simp_rw [qB_eval]
    have hs := card_matFiber_recurrence_succ (s := t + 1) σ hσ
    have hsq := congrArg (fun z : ℕ => (z : ℚ)) hs
    push_cast at hsq
    change ((matFiber n (t + 1 + 1) (t + 1 + 1) B).card : ℚ) -
      (matFiber n (t + 1) (t + 1) B).card -
      ∑ C ∈ nbSupp B (matSupport (permMatrix σ)),
        ((matFiber n (t + 1) (t + 1) C).card : ℚ) = 0
    linarith
  have hv := congrArg (fun p : Polynomial ℚ => p.eval x) hp
  simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_finsetSum,
    Polynomial.eval_zero] at hv
  linarith

theorem qB_eq_zero_of_not_support {n : ℕ} {B : Finset (Fin n × Fin n)}
    (h : ¬ IsSupport n B) : qB n B = 0 := by
  apply poly_eq_zero_of_nat_eval_eq_zero
  intro r
  rw [qB_eval]
  have hc : (matFiber n (r + 1) (r + 1) B).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    exact fun M hM => h ⟨r + 1, by omega, M, hM⟩
  simpa only [gB, hc, Nat.cast_zero]

/-- Boundary balance propagates the zero-level constants to reciprocity at
every rational argument. No dimension-sign assumption is used. -/
theorem normalized_reciprocity_of_boundaryBalance (n : ℕ) (hb : BoundaryBalance n) :
    ∀ B : Finset (Fin n × Fin n), ∀ x : ℚ,
      (qB n B).eval (-x - 1) = sB n B * (closedPoly n B).eval x := by
  classical
  intro B
  induction B using Finset.strongInductionOn with
  | _ B ih =>
    by_cases hB : IsSupport n B
    · have hperm : HasPerm n B := by
        obtain ⟨s, hs, M, hM⟩ := hB
        rw [matFiber, Finset.mem_filter] at hM
        obtain ⟨σ, hσ⟩ := exists_perm_support_subset_of_lineSums hs hM.2.1
        exact ⟨σ, hσ.trans_eq hM.2.2⟩
      obtain ⟨σ, hσ⟩ := hperm
      let R : Polynomial ℚ := (qB n B).comp (-X - 1)
      let Q : Polynomial ℚ := C (sB n B) * closedPoly n B
      have hp : R = Q := by
        apply polynomial_eq_of_eq_difference
        · intro x
          have hr := qB_rec_perm n B σ hσ (-x - 2)
          have harg : -x - 2 + 1 = -x - 1 := by ring
          rw [harg] at hr
          have hchildren :
              (∑ C ∈ nbSupp B (matSupport (permMatrix σ)), (qB n C).eval (-x - 2)) =
              ∑ C ∈ nbSupp B (matSupport (permMatrix σ)),
                sB n C * (closedPoly n C).eval (x + 1) := by
            apply Finset.sum_congr rfl
            intro C hC
            have hc := Finset.mem_erase.mp hC
            have hsub := (mem_fiberCandidates.mp hc.2).1
            have hsmall : C ⊂ B := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hc.1⟩
            have hi := ih C hsmall (x + 1)
            convert hi using 1 <;> congr 1 <;> ring
          rw [hchildren] at hr
          have hmem : B ∈ fiberCandidates B (matSupport (permMatrix σ)) :=
            mem_fiberCandidates.mpr ⟨Finset.Subset.refl _, Finset.sdiff_subset⟩
          have hbal :
              (∑ C ∈ nbSupp B (matSupport (permMatrix σ)),
                sB n C * (closedPoly n C).eval (x + 1)) +
                sB n B * (closedPoly n B).eval (x + 1) =
                sB n B * (closedPoly n B).eval x := by
            change (∑ C ∈ (fiberCandidates B (matSupport (permMatrix σ))).erase B,
              sB n C * (closedPoly n C).eval (x + 1)) + _ = _
            rw [Finset.sum_erase_add _ _ hmem]
            simpa only [add_sub_cancel_right] using hb B hB σ hσ (x + 1)
          simp only [R, Q, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_neg,
            Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C]
          have harg' : -(x + 1) - 1 = -x - 2 := by ring
          rw [harg']
          linarith
        · simp only [R, Q, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_neg,
            Polynomial.eval_X, Polynomial.eval_one, neg_zero, zero_sub,
            Polynomial.eval_mul, Polynomial.eval_C,
            closedPoly_eval_zero (show HasPerm n B from ⟨σ, hσ⟩), mul_one, sB]
      intro x
      have hx := congrArg (fun p : Polynomial ℚ => p.eval x) hp
      simpa only [R, Q, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_neg,
        Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C] using hx
    · intro x
      rw [qB_eq_zero_of_not_support hB, Polynomial.eval_zero,
        sB_eq_zero_of_not_isSupport hB, zero_mul]

/-- On the full board, normalized support reciprocity becomes the desired
reflection up to one scalar. Its sign can then be read from the leading term. -/
theorem semiMagic_normalized_reflection_of_boundaryBalance (n : ℕ) (hn : 1 ≤ n)
    (p : Polynomial ℚ)
    (hp : ∀ t : ℕ, p.eval (t : ℚ) = (MagicSquares.semiMagicCount n t : ℚ))
    (hb : BoundaryBalance n) : ∀ x : ℚ,
      p.eval (-(n : ℚ) - x) =
        sB n (Finset.univ : Finset (Fin n × Fin n)) * p.eval x := by
  classical
  let U : Finset (Fin n × Fin n) := Finset.univ
  have hperm : HasPerm n U := ⟨Equiv.refl _, Finset.subset_univ _⟩
  have hcp : closedPoly n U = p := by
    apply sub_eq_zero.mp
    apply poly_eq_zero_of_nat_eval_eq_zero
    intro t
    rw [Polynomial.eval_sub, closedPoly_eval_of_hasPerm hperm,
      show (closedFiber n t U).card = MagicSquares.semiMagicCount n t from
        card_closedFiber_univ n t, hp, sub_self]
  intro x
  have hs := congrArg (fun q : Polynomial ℚ => q.eval (-(n : ℚ) - x))
    (fullSupport_poly_shift n hn p hp)
  simp only [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one] at hs
  have harg : -(n : ℚ) - x + n - 1 = -x - 1 := by ring
  rw [harg] at hs
  rw [← hs]
  have hr := normalized_reciprocity_of_boundaryBalance n hb U x
  rw [hcp] at hr
  exact hr

end MagicSquaresSpencer
