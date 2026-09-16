import Mathlib
import Definitions.Def_MagicSquares

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

/-- The total is the sum of the `n` row sums, each equal to `s`. -/
theorem solution {n : ℕ} {α : Type*} [AddCommMonoid α]
    (M : Square n α) (s : α) (hM : IsSemiMagic M s) :
    totalSum M = n • s := by
  calc
    totalSum M = ∑ i : Fin n, rowSum M i := by simp [totalSum, rowSum]
    _ = ∑ i : Fin n, s := by simp [hM.1]
    _ = n • s := by
          rw [Finset.sum_const, Finset.card_univ]
          simp
