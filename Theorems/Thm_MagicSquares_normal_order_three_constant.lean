import Mathlib
import Definitions.Def_MagicSquares
import Theorems.Thm_MagicSquares_magic_constant_of_normal

set_option autoImplicit false

/-!
# `MagicSquares.normal_order_three_constant`

Local mirror of the platform theorem (id `b78210eb-e526-4997-b9c4-8ad93146ebad`
publish job), kept so that downstream reductions type-check locally.
-/

open MagicSquares

theorem normal_order_three_constant (M : Square 3 ℕ) (s : ℕ)
    (hN : IsNormal M) (hM : IsMagic M s) :
    s = 15 := by
  have h := magic_constant_of_normal 3 M s hN hM
  norm_num at h
  omega
