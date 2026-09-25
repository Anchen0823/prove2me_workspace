import Mathlib
import Definitions.Def_MagicSquares

set_option autoImplicit false

/-!
# Special classes of order-three magic squares

Missions I--III handled *counting* and *classifying* order-three magic squares.
This module sets up the two classical special classes that are singled out by
extra symmetry requirements:

* **panmagic (pandiagonal)** squares, where *every* broken diagonal -- not just
  the two main ones -- has the magic sum;
* **symmetric** squares, where the array equals its own transpose.

For order three both classes turn out to have a completely explicit shape. Let
`M` be a `3 × 3` array of nonnegative integers with line sum `3 * e`, written

$$M=\begin{pmatrix} a & b & c \\ d & e_{11} & f \\ g & h & i \end{pmatrix}.$$

*Panmagic.* Besides the twelve line sums there is nothing left to choose: the
broken diagonal `b + f + g` and the broken anti-diagonal `b + d + i` together
with the rows and columns force `a = b = c = d = e_{11} = f = g = h = i = e`.
So `constSquare3 e` -- the array all of whose entries are `e` -- is the only
panmagic square of line sum `3 * e`.

*Symmetric.* Symmetry identifies `b = d`, `c = g` and `f = h`, so only the five
cells `a, b, c, e_{11}, i` remain free; the anti-diagonal reads
`2 c + e_{11} = 3 e`. The four remaining line sums then give

$$\mathrm{symmMagic3}(e,a)=\begin{pmatrix}
a & 2e-a & e \\ 2e-a & e & a \\ e & a & 2e-a \end{pmatrix},$$

an array which is symmetric for every `a`, and admissible exactly when
`0 ≤ a ≤ 2 e`, i.e. for the `2 e + 1` values collected in `symmParamSet e`.

The two counting theorems built on these shapes are submitted separately.
-/

namespace MagicSquares

/-- The constant `3 × 3` array with every entry equal to `e`, read as an array
over `Fin (3 * e + 1)` -- the ambient type of the counting functions at line
sum `3 * e`. -/
def constSquare3 (e : ℕ) : Square 3 (Fin (3 * e + 1)) :=
  fun _ _ => ⟨e, by omega⟩

/-- The symmetric `3 × 3` shape of line sum `3 * e` attached to the free corner
parameter `a`. It is symmetric for every `a`; it is a square of nonnegative
integers of line sum `3 * e` exactly when `a ≤ 2 * e`. -/
def symmMagic3 (e a : ℕ) : Square 3 ℕ :=
  ![![a, 2 * e - a, e],
    ![2 * e - a, e, a],
    ![e, a, 2 * e - a]]

noncomputable section

/-- The admissible corner parameters of the symmetric family of line sum
`3 * e`, namely the `2 * e + 1` values `0, …, 2 * e`. -/
def symmParamSet (e : ℕ) : Finset ℕ := Finset.range (2 * e + 1)

/-- The number of admissible corner parameters of the symmetric family. -/
def symmParamCount (e : ℕ) : ℕ := (symmParamSet e).card

end

end MagicSquares
