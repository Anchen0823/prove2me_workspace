import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresParam3

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

namespace MagicSquares

/-- **6. 三参数构造满足幻方条件** — 充分性. -/
theorem magic_three_param_sufficient (e a c : ℕ) (h : IsParam3 e a c) :
    IsMagic (mkMagic3 e a c) (3 * e) := by
  rcases h with ⟨hl, hu, ha, hc⟩
  have ha2 : a ≤ 2 * e := by omega
  have hc2 : c ≤ 2 * e := by omega
  constructor
  · constructor
    · intro i
      fin_cases i <;> simp [mkMagic3, rowSum, Fin.sum_univ_three]
      all_goals omega
    · intro j
      fin_cases j <;> simp [mkMagic3, colSum, Fin.sum_univ_three]
      all_goals omega
  · constructor
    · simp [mkMagic3, diagSum, Fin.sum_univ_three]
      omega
    · simp [mkMagic3, antiDiagSum, Fin.sum_univ_three]
      omega

/-- **7. 任意三阶幻方都能还原为该构造** — 必要性. -/
theorem magic_three_param_necessary (e : ℕ) (M : Square 3 ℕ)
    (hM : IsMagic M (3 * e)) :
    M = mkMagic3 e (M 0 0) (M 0 2) := by
  have hR0 := hM.1.1 (0 : Fin 3)
  have hR1 := hM.1.1 (1 : Fin 3)
  have hR2 := hM.1.1 (2 : Fin 3)
  have hC0 := hM.1.2 (0 : Fin 3)
  have hC1 := hM.1.2 (1 : Fin 3)
  have hC2 := hM.1.2 (2 : Fin 3)
  have hD := hM.2.1
  have hA := hM.2.2
  simp [rowSum, colSum, diagSum, antiDiagSum, Fin.sum_univ_three] at *
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mkMagic3]
  all_goals omega

end MagicSquares
