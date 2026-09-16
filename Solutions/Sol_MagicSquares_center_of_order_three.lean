import Mathlib
import Definitions.Def_MagicSquares
open MagicSquares

/-- Solution for `MagicSquares.center_of_order_three`.

Add the middle row, the middle column and the two diagonals: the centre is
counted four times and every other cell exactly once, so the total is
`totalSum + 3 * centre = 3 * s + 3 * centre`; but it is also `4 * s`. -/
theorem solution (M : Square 3 ℕ) (s : ℕ) (hM : IsMagic M s) :
    3 * M 1 1 = s := by
  have hR0 : M 0 0 + M 0 1 + M 0 2 = s := by
    simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (0 : Fin 3)
  have hR1 : M 1 0 + M 1 1 + M 1 2 = s := by
    simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (1 : Fin 3)
  have hR2 : M 2 0 + M 2 1 + M 2 2 = s := by
    simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (2 : Fin 3)
  have hC1 : M 0 1 + M 1 1 + M 2 1 = s := by
    simpa [colSum, Fin.sum_univ_three] using hM.1.2 (1 : Fin 3)
  have hD : M 0 0 + M 1 1 + M 2 2 = s := by
    simpa [diagSum, Fin.sum_univ_three] using hM.2.1
  have hA : M 0 2 + M 1 1 + M 2 0 = s := by
    simpa [antiDiagSum, Fin.sum_univ_three] using hM.2.2
  omega
