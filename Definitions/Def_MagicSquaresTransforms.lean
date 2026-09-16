import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_MagicSquares

set_option autoImplicit false

/-! # Magic-square symmetries and elementary transformations

This module extends `Definitions.Def_MagicSquares` with the standard symmetries
(transpose, vertical/horizontal flips) and affine substitutions used in the
structural theory of magic squares.

Only the operations themselves and the explicit affine line-sum identities are
provided; permutation invariance of sums is used directly in theorem proofs.
-/

namespace MagicSquares

variable {n : ℕ} {α : Type*}

/-! ## Symmetries of the square -/

/-- The transpose of a square. -/
def transpose [AddCommMonoid α] (M : Square n α) : Square n α :=
  fun i j => M j i

/-- Vertical flip: reverse the order of the rows. -/
def flipVertical (M : Square n α) : Square n α :=
  fun i j => M (Fin.rev i) j

/-- Horizontal flip: reverse the order of the columns. -/
def flipHorizontal (M : Square n α) : Square n α :=
  fun i j => M i (Fin.rev j)

/-! ## Line sums under symmetries -/

section symmetry_lemmas
variable [AddCommMonoid α]

@[simp]
lemma rowSum_transpose (M : Square n α) (i : Fin n) :
    rowSum (transpose M) i = colSum M i := by
  simp [rowSum, colSum, transpose]

@[simp]
lemma colSum_transpose (M : Square n α) (j : Fin n) :
    colSum (transpose M) j = rowSum M j := by
  simp [rowSum, colSum, transpose]

@[simp]
lemma diagSum_transpose (M : Square n α) :
    diagSum (transpose M) = diagSum M := by
  simp [diagSum, transpose]

@[simp]
lemma antiDiagSum_transpose (M : Square n α) :
    antiDiagSum (transpose M) = antiDiagSum M := by
  simp only [antiDiagSum, transpose]
  rw [← Function.Bijective.sum_comp Fin.rev_bijective (fun i => M (Fin.rev i) i)]
  simp

@[simp]
lemma rowSum_flipVertical (M : Square n α) (i : Fin n) :
    rowSum (flipVertical M) i = rowSum M (Fin.rev i) := by
  simp [rowSum, flipVertical]

@[simp]
lemma colSum_flipVertical (M : Square n α) (j : Fin n) :
    colSum (flipVertical M) j = colSum M j := by
  simp only [colSum, flipVertical]
  rw [← Function.Bijective.sum_comp Fin.rev_bijective (fun i => M i j)]

@[simp]
lemma diagSum_flipVertical (M : Square n α) :
    diagSum (flipVertical M) = antiDiagSum M := by
  simp only [diagSum, antiDiagSum, flipVertical]
  rw [← Function.Bijective.sum_comp Fin.rev_bijective (fun i => M i (Fin.rev i))]
  simp

@[simp]
lemma antiDiagSum_flipVertical (M : Square n α) :
    antiDiagSum (flipVertical M) = diagSum M := by
  simp only [antiDiagSum, diagSum, flipVertical]
  rw [← Function.Bijective.sum_comp Fin.rev_bijective (fun i => M i i)]

@[simp]
lemma rowSum_flipHorizontal (M : Square n α) (i : Fin n) :
    rowSum (flipHorizontal M) i = rowSum M i := by
  simp only [rowSum, flipHorizontal]
  rw [← Function.Bijective.sum_comp Fin.rev_bijective (fun j => M i j)]

@[simp]
lemma colSum_flipHorizontal (M : Square n α) (j : Fin n) :
    colSum (flipHorizontal M) j = colSum M (Fin.rev j) := by
  simp [colSum, flipHorizontal]

@[simp]
lemma diagSum_flipHorizontal (M : Square n α) :
    diagSum (flipHorizontal M) = antiDiagSum M := by
  simp only [diagSum, antiDiagSum, flipHorizontal]

@[simp]
lemma antiDiagSum_flipHorizontal (M : Square n α) :
    antiDiagSum (flipHorizontal M) = diagSum M := by
  simp [antiDiagSum, diagSum, flipHorizontal]

@[simp]
lemma totalSum_transpose (M : Square n α) :
    totalSum (transpose M) = totalSum M := by
  simp only [totalSum, transpose]
  rw [Finset.sum_comm]

@[simp]
lemma totalSum_flipVertical (M : Square n α) :
    totalSum (flipVertical M) = totalSum M := by
  simp only [totalSum, flipVertical]
  rw [← Function.Bijective.sum_comp Fin.rev_bijective (fun i => ∑ j : Fin n, M i j)]

@[simp]
lemma totalSum_flipHorizontal (M : Square n α) :
    totalSum (flipHorizontal M) = totalSum M := by
  simp only [totalSum, flipHorizontal]
  congr with i
  rw [← Function.Bijective.sum_comp Fin.rev_bijective (fun j => M i j)]

end symmetry_lemmas

/-! ## Affine substitution -/

section affine_lemmas
variable [Semiring α]

/-- The affine transformation `M ↦ a • M + b` (entrywise). -/
def affine (a b : α) (M : Square n α) : Square n α :=
  fun i j => a * M i j + b

private lemma sum_const_fin (b : α) :
    ∑ _j : Fin n, b = n • b := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  all_goals simp

@[simp]
lemma rowSum_affine (M : Square n α) (a b : α) (i : Fin n) :
    rowSum (affine a b M) i = a * rowSum M i + n • b := by
  simp [rowSum, affine, Finset.mul_sum, Finset.sum_add_distrib, sum_const_fin]

@[simp]
lemma colSum_affine (M : Square n α) (a b : α) (j : Fin n) :
    colSum (affine a b M) j = a * colSum M j + n • b := by
  simp [colSum, affine, Finset.mul_sum, Finset.sum_add_distrib, sum_const_fin]

@[simp]
lemma diagSum_affine (M : Square n α) (a b : α) :
    diagSum (affine a b M) = a * diagSum M + n • b := by
  simp [diagSum, affine, Finset.mul_sum, Finset.sum_add_distrib, sum_const_fin]

@[simp]
lemma antiDiagSum_affine (M : Square n α) (a b : α) :
    antiDiagSum (affine a b M) = a * antiDiagSum M + n • b := by
  simp [antiDiagSum, affine, Finset.mul_sum, Finset.sum_add_distrib, sum_const_fin]

end affine_lemmas

end MagicSquares
