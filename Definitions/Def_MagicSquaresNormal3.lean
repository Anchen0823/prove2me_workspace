import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresParam3

set_option autoImplicit false

/-!
# Normal order-three magic squares: the parameter pairs that survive

MacMahon's parametrization writes every order-three magic square of line sum
`3 * e` as `mkMagic3 e a c`, with `(a, c)` in the finite set `paramSet e`. A
square is **normal** when its nine entries are exactly `1, …, 9`, each once
(`IsNormal`).

For `e = 5` the line sum is `15`, the magic constant of a normal square of order
three, and the classification problem is to decide which admissible pairs give a
normal square. `normalParamSet e` collects them.

The set is defined with `classical` because `IsNormal` — being stated with a
`Function.Injective` — carries no decidable instance, so the `filter` cannot be
formed constructively. The classification itself (`magic_three_normal_eight`)
shows that `normalParamSet 5` has exactly eight elements.
-/

namespace MagicSquares

noncomputable section

/-- The admissible parameter pairs whose MacMahon square is normal. -/
def normalParamSet (e : ℕ) : Finset (ℕ × ℕ) :=
  by
    classical
    exact (paramSet e).filter fun ac => IsNormal (mkMagic3 e ac.1 ac.2)

/-- The number of admissible parameter pairs giving a normal square. -/
def normalParamCount (e : ℕ) : ℕ := (normalParamSet e).card

end

end MagicSquares
