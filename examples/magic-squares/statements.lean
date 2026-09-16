import Mathlib
import Definitions.Def_MagicSquares
open MagicSquares

namespace MagicSquares

theorem magic_constant_of_normal (n : ℕ) (M : Square n ℕ) (s : ℕ)
    (hN : IsNormal M) (hM : IsMagic M s) :
    2 * s = n * (n ^ 2 + 1) := by sorry

end MagicSquares

namespace MagicSquares

theorem center_of_order_three (M : Square 3 ℕ) (s : ℕ)
    (hM : IsMagic M s) :
    3 * M 1 1 = s := by sorry

end MagicSquares

namespace MagicSquares

theorem normal_order_two_none :
    ¬ ∃ (M : Square 2 ℕ) (s : ℕ), IsNormal M ∧ IsMagic M s := by sorry

end MagicSquares

namespace MagicSquares

theorem magic_count_three_divisible (e : ℕ) :
    magicCount 3 (3 * e) = 2 * e ^ 2 + 2 * e + 1 := by sorry

end MagicSquares

namespace MagicSquares

theorem magic_count_three_otherwise (t : ℕ) (ht : ¬ 3 ∣ t) :
    magicCount 3 t = 0 := by sorry

end MagicSquares

namespace MagicSquares

theorem semi_magic_count_three (t : ℕ) :
    semiMagicCount 3 t = 3 * ((t + 3).choose 4) + ((t + 2).choose 2) := by sorry

end MagicSquares
