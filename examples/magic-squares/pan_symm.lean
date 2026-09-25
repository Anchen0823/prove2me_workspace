import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresParam3
import Definitions.Def_MagicSquaresSpecial3
import Theorems.Thm_MagicSquares_center_of_order_three

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

/-- `MagicSquares.pan_three_card`: the only panmagic `3 × 3` square of line sum
`3 * e` is the constant square. The twelve line sums leave no freedom: the six
broken diagonals together with the rows and columns force every entry to be `e`. -/
theorem pan_three_card (e : ℕ) : panMagicCount 3 (3 * e) = 1 := by
  classical
  rw [panMagicCount, panMagicSquares]
  rw [Finset.card_eq_one]
  refine ⟨constSquare3 e, ?_⟩
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  · -- the constant square is panmagic
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨fun i => ?_, fun j => ?_⟩, fun k => ?_, fun k => ?_⟩
    · simp [rowSum, constSquare3]
    · simp [colSum, constSquare3]
    · fin_cases k <;> simp [brokenDiagSum, constSquare3]
    · fin_cases k <;> simp [brokenAntiDiagSum, constSquare3]
  · -- and it is the only one
    intro M hM
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM
    have hR0 : (M 0 0 : ℕ) + (M 0 1 : ℕ) + (M 0 2 : ℕ) = 3 * e := by
      simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (0 : Fin 3)
    have hR1 : (M 1 0 : ℕ) + (M 1 1 : ℕ) + (M 1 2 : ℕ) = 3 * e := by
      simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (1 : Fin 3)
    have hR2 : (M 2 0 : ℕ) + (M 2 1 : ℕ) + (M 2 2 : ℕ) = 3 * e := by
      simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (2 : Fin 3)
    have hC0 : (M 0 0 : ℕ) + (M 1 0 : ℕ) + (M 2 0 : ℕ) = 3 * e := by
      simpa [colSum, Fin.sum_univ_three] using hM.1.2 (0 : Fin 3)
    have hC1 : (M 0 1 : ℕ) + (M 1 1 : ℕ) + (M 2 1 : ℕ) = 3 * e := by
      simpa [colSum, Fin.sum_univ_three] using hM.1.2 (1 : Fin 3)
    have hC2 : (M 0 2 : ℕ) + (M 1 2 : ℕ) + (M 2 2 : ℕ) = 3 * e := by
      simpa [colSum, Fin.sum_univ_three] using hM.1.2 (2 : Fin 3)
    have hB0 : (M 0 0 : ℕ) + (M 1 1 : ℕ) + (M 2 2 : ℕ) = 3 * e := by
      have h := hM.2.1 (0 : Fin 3)
      simpa [brokenDiagSum, Fin.sum_univ_three] using h
    have hB1 : (M 0 1 : ℕ) + (M 1 2 : ℕ) + (M 2 0 : ℕ) = 3 * e := by
      have h := hM.2.1 (1 : Fin 3)
      simpa [brokenDiagSum, Fin.sum_univ_three] using h
    have hB2 : (M 0 2 : ℕ) + (M 1 0 : ℕ) + (M 2 1 : ℕ) = 3 * e := by
      have h := hM.2.1 (2 : Fin 3)
      simpa [brokenDiagSum, Fin.sum_univ_three] using h
    have hA0 : (M 0 2 : ℕ) + (M 1 1 : ℕ) + (M 2 0 : ℕ) = 3 * e := by
      have h := hM.2.2 (0 : Fin 3)
      simpa [brokenAntiDiagSum, Fin.sum_univ_three] using h
    have hA1 : (M 0 0 : ℕ) + (M 1 2 : ℕ) + (M 2 1 : ℕ) = 3 * e := by
      have h := hM.2.2 (1 : Fin 3)
      simpa [brokenAntiDiagSum, Fin.sum_univ_three] using h
    have hA2 : (M 0 1 : ℕ) + (M 1 0 : ℕ) + (M 2 2 : ℕ) = 3 * e := by
      have h := hM.2.2 (2 : Fin 3)
      simpa [brokenAntiDiagSum, Fin.sum_univ_three] using h
    ext i j
    fin_cases i <;> fin_cases j <;> (simp [constSquare3]; omega)
