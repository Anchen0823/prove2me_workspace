import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresParam3

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

namespace MagicSquares

/-- Local mirror of the platform theorem `magic_three_param_necessary`
(id `4e513d72-b4b7-419b-a0e6-dc115ee77a94`), proved on the platform. -/
theorem magic_three_param_necessary (e : ℕ) (M : Square 3 ℕ)
    (hM : IsMagic M (3 * e)) :
    M = mkMagic3 e (M 0 0) (M 0 2) := by
  have hR0 : M 0 0 + M 0 1 + M 0 2 = 3 * e := by
    simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (0 : Fin 3)
  have hR1 : M 1 0 + M 1 1 + M 1 2 = 3 * e := by
    simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (1 : Fin 3)
  have hR2 : M 2 0 + M 2 1 + M 2 2 = 3 * e := by
    simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (2 : Fin 3)
  have hC0 : M 0 0 + M 1 0 + M 2 0 = 3 * e := by
    simpa [colSum, Fin.sum_univ_three] using hM.1.2 (0 : Fin 3)
  have hC1 : M 0 1 + M 1 1 + M 2 1 = 3 * e := by
    simpa [colSum, Fin.sum_univ_three] using hM.1.2 (1 : Fin 3)
  have hC2 : M 0 2 + M 1 2 + M 2 2 = 3 * e := by
    simpa [colSum, Fin.sum_univ_three] using hM.1.2 (2 : Fin 3)
  have hD : M 0 0 + M 1 1 + M 2 2 = 3 * e := by
    simpa [diagSum, Fin.sum_univ_three] using hM.2.1
  have hA : M 0 2 + M 1 1 + M 2 0 = 3 * e := by
    simpa [antiDiagSum, Fin.sum_univ_three] using hM.2.2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mkMagic3]
  all_goals omega

end MagicSquares
