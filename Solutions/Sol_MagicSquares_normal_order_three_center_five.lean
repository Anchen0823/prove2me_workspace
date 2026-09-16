import Mathlib
import Definitions.Def_MagicSquares
import Theorems.Thm_MagicSquares_center_of_order_three
import Theorems.Thm_MagicSquares_normal_order_three_constant

set_option autoImplicit false

open MagicSquares

/-- Reduction of `MagicSquares.normal_order_three_center_five` to
`MagicSquares.normal_order_three_constant` and `MagicSquares.center_of_order_three`.

MacMahon's centre identity gives `3 * M 1 1 = s`, and normality fixes `s = 15`;
hence `M 1 1 = 5`. -/
theorem solution (M : Square 3 ℕ) (s : ℕ) (hN : IsNormal M) (hM : IsMagic M s) :
    M 1 1 = 5 := by
  have hs := normal_order_three_constant M s hN hM
  have hc := center_of_order_three M s hM
  omega
