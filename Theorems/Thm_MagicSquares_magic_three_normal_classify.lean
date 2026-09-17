import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresParam3

set_option autoImplicit false

namespace MagicSquares

/-- Local mirror of the platform theorem magic_three_normal_classify (id
`c677420b-bca2-41da-b9e3-f804919a1235`). Body is `sorry` here; kept only so
downstream reductions type-check locally. -/
theorem magic_three_normal_classify (a c : ℕ) (_hac : (a, c) ∈ paramSet 5) :
    IsNormal (mkMagic3 5 a c) ↔
      (a = 2 ∧ c = 4) ∨ (a = 2 ∧ c = 6) ∨ (a = 4 ∧ c = 2) ∨ (a = 4 ∧ c = 8) ∨
        (a = 6 ∧ c = 2) ∨ (a = 6 ∧ c = 8) ∨ (a = 8 ∧ c = 4) ∨ (a = 8 ∧ c = 6) := by
  sorry

end MagicSquares
