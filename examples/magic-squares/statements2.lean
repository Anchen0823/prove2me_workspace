import Mathlib
import Definitions.Def_MagicSquares
open MagicSquares

namespace MagicSquares

theorem normal_order_three_constant (M : Square 3 ℕ) (s : ℕ)
    (hN : IsNormal M) (hM : IsMagic M s) :
    s = 15 := by sorry

end MagicSquares

namespace MagicSquares

theorem normal_order_three_center_five (M : Square 3 ℕ) (s : ℕ)
    (hN : IsNormal M) (hM : IsMagic M s) :
    M 1 1 = 5 := by sorry

end MagicSquares

namespace MagicSquares

theorem normal_order_three_associative (M : Square 3 ℕ) (s : ℕ)
    (hN : IsNormal M) (hM : IsMagic M s) :
    IsAssociative M 10 := by sorry

end MagicSquares

namespace MagicSquares

theorem panmagic_is_magic {n : ℕ} [NeZero n]
    (M : Square n ℕ) (s : ℕ) (hP : IsPanMagic M s) :
    IsMagic M s := by sorry

end MagicSquares
