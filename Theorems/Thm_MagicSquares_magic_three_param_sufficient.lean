import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresParam3

set_option autoImplicit false

open MagicSquares
open scoped BigOperators

namespace MagicSquares

/-- Local mirror of the platform theorem `magic_three_param_sufficient` (id `665c40f1-688c-4f40-aafb-1b8d82bbeb35`),
proved on the platform; kept here so downstream reductions type-check locally. -/
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

end MagicSquares
