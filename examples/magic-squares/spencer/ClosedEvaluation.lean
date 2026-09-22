import examples.«magic-squares».spencer.ClosedPolynomial

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace MagicSquaresSpencer

open Finset Polynomial

/-- The counting polynomial of an admissible board; zero for an inadmissible board.
The latter convention represents positive levels only. -/
noncomputable def closedPoly (n : ℕ) (B : Finset (Fin n × Fin n)) : Polynomial ℚ := by
  classical
  exact if h : HasPerm n B then Classical.choose (exists_polynomial_closedFiber n B h) else 0

theorem closedPoly_eval_of_hasPerm {n : ℕ} {B : Finset (Fin n × Fin n)}
    (h : HasPerm n B) (t : ℕ) :
    (closedPoly n B).eval (t : ℚ) = (closedFiber n t B).card := by
  simp only [closedPoly, dif_pos h]
  exact Classical.choose_spec (exists_polynomial_closedFiber n B h) t

theorem closedPoly_eval_pos (n t : ℕ) (B : Finset (Fin n × Fin n)) :
    (closedPoly n B).eval ((t + 1 : ℕ) : ℚ) = (closedFiber n (t + 1) B).card := by
  classical
  by_cases h : HasPerm n B
  · exact closedPoly_eval_of_hasPerm h (t + 1)
  · rw [closedPoly, dif_neg h, Polynomial.eval_zero,
      closedFiber_eq_empty_of_no_perm (by omega) (fun σ hσ => h ⟨σ, hσ⟩)]
    simp

theorem card_closedFiber_zero (n : ℕ) (B : Finset (Fin n × Fin n)) :
    (closedFiber n 0 B).card = 1 := by
  classical
  have hset : closedFiber n 0 B = {0} := by
    ext M
    rw [mem_closedFiber, matBoxLine, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hbox, -⟩, -⟩
      funext i j
      exact Nat.eq_zero_of_le_zero ((mem_matBox.mp hbox) i j)
    · rintro rfl
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [mem_matBox]; intro i j; simp
      · exact ⟨fun i => by simp, fun j => by simp⟩
      · simp [matSupport]
  rw [hset, Finset.card_singleton]

theorem closedPoly_eval_zero {n : ℕ} {B : Finset (Fin n × Fin n)} (h : HasPerm n B) :
    (closedPoly n B).eval 0 = 1 := by
  simpa only [Nat.cast_zero, card_closedFiber_zero, Nat.cast_one] using
    closedPoly_eval_of_hasPerm h 0

/-- The boundary recurrence holds at rational arguments after polynomial extension. -/
theorem closedPoly_recurrence (n : ℕ) (B : Finset (Fin n × Fin n))
    (σ : Equiv.Perm (Fin n)) (hσ : matSupport (permMatrix σ) ⊆ B) (x : ℚ) :
    (closedPoly n B).eval (x + 1) = (closedPoly n B).eval x +
      ∑ S ∈ (matSupport (permMatrix σ)).powerset.filter (·.Nonempty),
        (-1 : ℚ) ^ (S.card + 1) * (closedPoly n (B \ S)).eval (x + 1) := by
  classical
  let R : Polynomial ℚ :=
    ∑ S ∈ (matSupport (permMatrix σ)).powerset.filter (·.Nonempty),
      C ((-1 : ℚ) ^ (S.card + 1)) * (closedPoly n (B \ S)).comp (X + 1)
  have hid : (closedPoly n B).comp (X + 1) - closedPoly n B - R = 0 := by
    apply poly_eq_zero_of_nat_eval_eq_zero
    intro t
    simp only [R, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C]
    have hc : (t : ℚ) + 1 = ((t + 1 : ℕ) : ℚ) := by simp
    rw [hc, closedPoly_eval_of_hasPerm ⟨σ, hσ⟩ t, closedPoly_eval_pos]
    simp_rw [closedPoly_eval_pos]
    rw [closedFiber_card_recurrence n t B σ hσ]
    ring
  have hv := congrArg (fun P : Polynomial ℚ => P.eval x) hid
  simp only [R, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_zero] at hv
  linarith

theorem sum_nonempty_subsets_sign {α : Type*} [DecidableEq α]
    (φ : Finset α) (hφ : φ.Nonempty) :
    ∑ S ∈ φ.powerset.filter (·.Nonempty), (-1 : ℚ) ^ (S.card + 1) = 1 := by
  have h := card_filter_subset_not_subset_eq_sum_card_filter_subset_sdiff
    ({()} : Finset Unit) (fun _ => (∅ : Finset α)) ∅ φ
  simpa [hφ.ne_empty] using h.symm

end MagicSquaresSpencer
