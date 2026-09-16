import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresParam3

namespace MagicSquares

theorem magic_three_param_sufficient (e a c : ℕ) (h : IsParam3 e a c) :
    IsMagic (mkMagic3 e a c) (3 * e) := by sorry

end MagicSquares

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresParam3

namespace MagicSquares

theorem magic_three_param_necessary (e : ℕ) (M : Square 3 ℕ)
    (hM : IsMagic M (3 * e)) :
    M = mkMagic3 e (M 0 0) (M 0 2) := by sorry

end MagicSquares
