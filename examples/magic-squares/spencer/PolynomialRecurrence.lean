import examples.«magic-squares».spencer.Spencer

set_option autoImplicit false

namespace MagicSquaresSpencer

open Polynomial Finset

/-- A polynomial forward difference determines a polynomial sequence, including its
initial value. The difference is evaluated at the new level. -/
theorem exists_poly_of_forward_difference (b : ℕ → ℚ) (P : Polynomial ℚ)
    (h : ∀ t : ℕ, b (t + 1) = b t + P.eval ((t + 1 : ℕ) : ℚ)) :
    ∃ Q : Polynomial ℚ, ∀ t : ℕ, Q.eval (t : ℚ) = b t := by
  let R := P.comp (X + 1)
  refine ⟨C (b 0) + antideriv R, ?_⟩
  intro t
  rw [Polynomial.eval_add, Polynomial.eval_C, antideriv_eval]
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih, h]
    simp [R, Polynomial.eval_comp, Nat.cast_add, Nat.cast_one]

/-- Induction for closed-support counts. Bad boards need only vanish at positive
levels, so their exceptional zero matrix never enters the forward difference. -/
theorem exists_poly_of_board_recurrence {α : Type*} [DecidableEq α]
    (b : Finset α → ℕ → ℚ) (good : Finset α → Prop)
    (terms : Finset α → Finset (Finset α))
    (child : Finset α → Finset α → Finset α)
    (weight : Finset α → Finset α → ℚ)
    (smaller : ∀ B C, C ∈ terms B → child B C ⊂ B)
    (bad : ∀ B, ¬ good B → ∀ t : ℕ, b B (t + 1) = 0)
    (recurrence : ∀ B, good B → ∀ t : ℕ,
      b B (t + 1) = b B t + ∑ C ∈ terms B, weight B C * b (child B C) (t + 1)) :
    ∀ B, good B → ∃ Q : Polynomial ℚ, ∀ t : ℕ, Q.eval (t : ℚ) = b B t := by
  classical
  intro B
  induction B using Finset.strongInductionOn with
  | _ B ih =>
    intro hB
    have hp : ∀ C ∈ terms B, ∃ P : Polynomial ℚ,
        ∀ t : ℕ, P.eval ((t + 1 : ℕ) : ℚ) = b (child B C) (t + 1) := by
      intro C hC
      by_cases hg : good (child B C)
      · obtain ⟨P, hP⟩ := ih (child B C) (smaller B C hC) hg
        exact ⟨P, fun t => hP (t + 1)⟩
      · exact ⟨0, fun t => by simp [bad (child B C) hg t]⟩
    choose P hP using hp
    let R : Polynomial ℚ := ∑ C ∈ (terms B).attach,
      Polynomial.C (weight B C.val) * P C.val C.property
    apply exists_poly_of_forward_difference (b B) R
    intro t
    rw [recurrence B hB t]
    congr 1
    simp only [R, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
    simp_rw [hP]
    exact (Finset.sum_attach _ _).symm

end MagicSquaresSpencer
