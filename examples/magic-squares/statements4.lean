import Mathlib
import Definitions.Def_MagicSquares

namespace MagicSquares

theorem total_sum_eq_n_line_sum {n : ℕ} {α : Type*} [AddCommMonoid α]
    (M : Square n α) (s : α) (hM : IsSemiMagic M s) :
    totalSum M = n • s := by sorry

end MagicSquares

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresTransforms

namespace MagicSquares

theorem transpose_preserves_magic {n : ℕ} {α : Type*} [AddCommMonoid α]
    (M : Square n α) (s : α) (hM : IsMagic M s) :
    IsMagic (transpose M) s := by sorry

end MagicSquares

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresTransforms

namespace MagicSquares

theorem flipVertical_preserves_magic {n : ℕ} {α : Type*} [AddCommMonoid α]
    (M : Square n α) (s : α) (hM : IsMagic M s) :
    IsMagic (flipVertical M) s := by sorry

end MagicSquares

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresTransforms

namespace MagicSquares

theorem flipHorizontal_preserves_magic {n : ℕ} {α : Type*} [AddCommMonoid α]
    (M : Square n α) (s : α) (hM : IsMagic M s) :
    IsMagic (flipHorizontal M) s := by sorry

end MagicSquares

import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresTransforms

namespace MagicSquares

theorem affine_preserves_magic {n : ℕ} {α : Type*} [Semiring α]
    (M : Square n α) (s a b : α) (hM : IsMagic M s) :
    IsMagic (affine a b M) (a * s + n • b) := by sorry

end MagicSquares

import Mathlib
import Definitions.Def_MagicSquares

namespace MagicSquares

theorem order_three_opposite_sum_eq_twice_center
    (M : Square 3 ℕ) (s : ℕ) (hM : IsMagic M s) (i j : Fin 3) :
    M i j + M (Fin.rev i) (Fin.rev j) = 2 * M 1 1 := by sorry

end MagicSquares
