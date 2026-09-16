import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresTransforms
import Theorems.Thm_MagicSquares_center_of_order_three

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

namespace MagicSquares

/-! ## 辅助引理：对称性对线的作用 -/

section helpers
variable {n : ℕ} {α : Type*} [AddCommMonoid α]

private lemma rowSum_transpose' (M : Square n α) (i : Fin n) :
    rowSum (transpose M) i = colSum M i := by
  simp [rowSum, colSum, transpose]

private lemma colSum_transpose' (M : Square n α) (j : Fin n) :
    colSum (transpose M) j = rowSum M j := by
  simp [rowSum, colSum, transpose]

private lemma diagSum_transpose' (M : Square n α) :
    diagSum (transpose M) = diagSum M := by
  simp [diagSum, transpose]

private lemma antiDiagSum_transpose' (M : Square n α) :
    antiDiagSum (transpose M) = antiDiagSum M := by
  simp only [antiDiagSum, transpose]
  rw [← Function.Bijective.sum_comp Fin.rev_bijective (fun i => M (Fin.rev i) i)]
  simp

private lemma rowSum_flipVertical' (M : Square n α) (i : Fin n) :
    rowSum (flipVertical M) i = rowSum M (Fin.rev i) := by
  simp [rowSum, flipVertical]

private lemma colSum_flipVertical' (M : Square n α) (j : Fin n) :
    colSum (flipVertical M) j = colSum M j := by
  simp only [colSum, flipVertical]
  rw [← Function.Bijective.sum_comp Fin.rev_bijective (fun i => M i j)]

private lemma diagSum_flipVertical' (M : Square n α) :
    diagSum (flipVertical M) = antiDiagSum M := by
  simp only [diagSum, antiDiagSum, flipVertical]
  rw [← Function.Bijective.sum_comp Fin.rev_bijective (fun i => M i (Fin.rev i))]
  simp

private lemma antiDiagSum_flipVertical' (M : Square n α) :
    antiDiagSum (flipVertical M) = diagSum M := by
  simp only [antiDiagSum, diagSum, flipVertical]
  rw [← Function.Bijective.sum_comp Fin.rev_bijective (fun i => M i i)]

private lemma rowSum_flipHorizontal' (M : Square n α) (i : Fin n) :
    rowSum (flipHorizontal M) i = rowSum M i := by
  simp only [rowSum, flipHorizontal]
  rw [← Function.Bijective.sum_comp Fin.rev_bijective (fun j => M i j)]

private lemma colSum_flipHorizontal' (M : Square n α) (j : Fin n) :
    colSum (flipHorizontal M) j = colSum M (Fin.rev j) := by
  simp [colSum, flipHorizontal]

private lemma diagSum_flipHorizontal' (M : Square n α) :
    diagSum (flipHorizontal M) = antiDiagSum M := by
  simp only [diagSum, antiDiagSum, flipHorizontal]

private lemma antiDiagSum_flipHorizontal' (M : Square n α) :
    antiDiagSum (flipHorizontal M) = diagSum M := by
  simp [antiDiagSum, diagSum, flipHorizontal]

end helpers

/-! ## 1. 行和汇总 -/

theorem total_sum_eq_n_line_sum {n : ℕ} {α : Type*} [AddCommMonoid α]
    (M : Square n α) (s : α) (hM : IsSemiMagic M s) :
    totalSum M = n • s := by
  calc
    totalSum M = ∑ i : Fin n, rowSum M i := by simp [totalSum, rowSum]
    _ = ∑ i : Fin n, s := by simp [hM.1]
    _ = n • s := by
          rw [Finset.sum_const, Finset.card_univ]
          simp

/-! ## 2. 转置 / 翻转保持幻方 -/

theorem transpose_preserves_magic {n : ℕ} {α : Type*} [AddCommMonoid α]
    (M : Square n α) (s : α) (hM : IsMagic M s) :
    IsMagic (transpose M) s := by
  constructor
  · constructor
    · intro i
      simpa [rowSum_transpose'] using hM.1.2 i
    · intro j
      simpa [colSum_transpose'] using hM.1.1 j
  · constructor
    · simpa [diagSum_transpose'] using hM.2.1
    · simpa [antiDiagSum_transpose'] using hM.2.2

theorem flipVertical_preserves_magic {n : ℕ} {α : Type*} [AddCommMonoid α]
    (M : Square n α) (s : α) (hM : IsMagic M s) :
    IsMagic (flipVertical M) s := by
  constructor
  · constructor
    · intro i
      simpa [rowSum_flipVertical'] using hM.1.1 (Fin.rev i)
    · intro j
      simpa [colSum_flipVertical'] using hM.1.2 j
  · constructor
    · simpa [diagSum_flipVertical'] using hM.2.2
    · simpa [antiDiagSum_flipVertical'] using hM.2.1

theorem flipHorizontal_preserves_magic {n : ℕ} {α : Type*} [AddCommMonoid α]
    (M : Square n α) (s : α) (hM : IsMagic M s) :
    IsMagic (flipHorizontal M) s := by
  constructor
  · constructor
    · intro i
      simpa [rowSum_flipHorizontal'] using hM.1.1 i
    · intro j
      simpa [colSum_flipHorizontal'] using hM.1.2 (Fin.rev j)
  · constructor
    · simpa [diagSum_flipHorizontal'] using hM.2.2
    · simpa [antiDiagSum_flipHorizontal'] using hM.2.1

/-! ## 3. 仿射变换保持等和性 -/

theorem affine_preserves_magic {n : ℕ} {α : Type*} [Semiring α]
    (M : Square n α) (s a b : α) (hM : IsMagic M s) :
    IsMagic (affine a b M) (a * s + n • b) := by
  constructor
  · constructor
    · intro i
      rw [rowSum_affine]
      rw [hM.1.1 i]
      ring
    · intro j
      rw [colSum_affine]
      rw [hM.1.2 j]
      ring
  · constructor
    · rw [diagSum_affine]
      rw [hM.2.1]
      ring
    · rw [antiDiagSum_affine]
      rw [hM.2.2]
      ring

/-! ## 5. 三阶中心对称格之和为 2A₁₁ -/

theorem order_three_opposite_sum_eq_twice_center
    (M : Square 3 ℕ) (s : ℕ) (hM : IsMagic M s) (i j : Fin 3) :
    M i j + M (Fin.rev i) (Fin.rev j) = 2 * M 1 1 := by
  have hR0 := hM.1.1 (0 : Fin 3)
  have hR1 := hM.1.1 (1 : Fin 3)
  have hR2 := hM.1.1 (2 : Fin 3)
  have hC0 := hM.1.2 (0 : Fin 3)
  have hC1 := hM.1.2 (1 : Fin 3)
  have hC2 := hM.1.2 (2 : Fin 3)
  have hD := hM.2.1
  have hA := hM.2.2
  simp [rowSum, colSum, diagSum, antiDiagSum, Fin.sum_univ_three] at *
  fin_cases i <;> fin_cases j <;> omega

end MagicSquares
