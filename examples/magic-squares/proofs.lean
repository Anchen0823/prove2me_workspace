import Mathlib
import Definitions.Def_MagicSquares
open MagicSquares

namespace MagicSquares

theorem center_of_order_three (M : Square 3 ℕ) (s : ℕ) (hM : IsMagic M s) :
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

theorem normal_order_two_none :
    ¬ ∃ (M : Square 2 ℕ) (s : ℕ), IsNormal M ∧ IsMagic M s := by
  rintro ⟨M, s, hN, hM⟩
  have hrow : M 0 0 + M 0 1 = s := by
    simpa [rowSum, Fin.sum_univ_two] using hM.1.1 (0 : Fin 2)
  have hdiag : M 0 0 + M 1 1 = s := by
    simpa [diagSum, Fin.sum_univ_two] using hM.2.1
  have hboth : M 0 0 + M 0 1 = M 0 0 + M 1 1 := by rw [hrow, hdiag]
  have heq : M 0 1 = M 1 1 := Nat.add_left_cancel hboth
  have hp : ((0 : Fin 2), (1 : Fin 2)) = ((1 : Fin 2), (1 : Fin 2)) := hN.2 heq
  exact (by decide : (0 : Fin 2) ≠ (1 : Fin 2)) (congrArg Prod.fst hp)

end MagicSquares
