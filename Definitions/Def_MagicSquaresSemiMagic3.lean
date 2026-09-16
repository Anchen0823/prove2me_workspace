import Mathlib
import Definitions.Def_MagicSquares

set_option autoImplicit false

open scoped BigOperators

/-!
# Order-three semi-magic squares: the permutation-matrix parametrization

Let $H_{3}(t)$ be the number of $3\times3$ arrays of nonnegative integers whose
three rows and three columns all sum to $t$ (the diagonals are unconstrained and
entries need not be distinct). MacMahon (1915) computed

$$H_{3}(t) = 3\binom{t+3}{4} + \binom{t+2}{2},$$

in contrast with the *magic* count $M_{3}(t)$, which is only a
quasi-polynomial. This module sets up the parametrization behind that formula.

## The six permutation matrices

Label the three "even" transversals (the identity and the two $3$-cycles)

$$D=\\{00,11,22\\},\qquad E=\\{01,12,20\\},\qquad F=\\{02,10,21\\},$$

and the three "odd" ones (the transpositions)

$$A=\\{00,12,21\\},\qquad B=\\{02,11,20\\},\qquad C=\\{01,10,22\\}.$$

Each of the six is the support of a $3\times3$ permutation matrix. Writing
$u,v,w$ for the multiplicities of the even ones and $x,y,z$ for the odd ones,
the array `sm3Of u v w x y z` is the corresponding linear combination; all six
line sums equal $u+v+w+x+y+z$, so it is semi-magic (`sm3Of_semiMagic`).

## The canonical form

Every $3\times3$ semi-magic square arises this way, and — after subtracting
$u=\min D$, $v=\min E$, $w=\min F$ — the residual odd multiplicities
$(x,y,z)$ satisfy $\min(x,y,z)=0$. That normalization makes the
representation *unique*; without it the relation

$$1\cdot D + 1\cdot E + 1\cdot F = 1\cdot A + 1\cdot B + 1\cdot C \;(=J)$$

would identify distinct $6$-tuples. `sm3Params t` is the resulting finite
parameter set and `sm3Count t` its cardinality. The two substantive statements
— that `sm3Of` is a bijection onto the semi-magic squares, and the evaluation
$\mathrm{sm3Count}(t) = 3\binom{t+3}{4}+\binom{t+2}{2}$ — are submitted
separately as theorems.
-/

namespace MagicSquares

/-- The $3\times3$ array obtained by adding the six order-three permutation
matrices with multiplicities `u v w` (the even transversals $D,E,F$) and
`x y z` (the odd ones $A,B,C$), as in the module docstring:

     ( u+x   v+z   w+y )
     ( w+z   u+y   v+x )
     ( v+y   w+x   u+z )

Every row and column sums to `u + v + w + x + y + z`. -/
def sm3Of (u v w x y z : ℕ) : Square 3 ℕ :=
  ![![u + x, v + z, w + y],
    ![w + z, u + y, v + x],
    ![v + y, w + x, u + z]]

/-- `sm3Of` read from a coefficient vector `p : Fin 6 → ℕ`, with `p 0 = u`,
`p 1 = v`, `p 2 = w`, `p 3 = x`, `p 4 = y`, `p 5 = z`. -/
def sm3OfFun (p : Fin 6 → ℕ) : Square 3 ℕ :=
  sm3Of (p 0) (p 1) (p 2) (p 3) (p 4) (p 5)

/-- The coefficient vector of `sm3Of`. -/
def sm3Coeffs (u v w x y z : ℕ) : Fin 6 → ℕ :=
  ![u, v, w, x, y, z]

/-- `sm3Of` is a semi-magic square of line sum `u + v + w + x + y + z`. -/
theorem sm3Of_semiMagic (u v w x y z : ℕ) :
    IsSemiMagic (sm3Of u v w x y z) (u + v + w + x + y + z) := by
  constructor
  · intro i
    fin_cases i <;> simp [rowSum, sm3Of, Fin.sum_univ_three] <;> omega
  · intro j
    fin_cases j <;> simp [colSum, sm3Of, Fin.sum_univ_three] <;> omega

/-- The three even transversals of a $3\times3$ array, as the triple of minima
that the canonical decomposition subtracts. -/
def sm3EvenMin (M : Square 3 ℕ) : ℕ × ℕ × ℕ :=
  (min (M 0 0) (min (M 1 1) (M 2 2)),
    min (M 0 1) (min (M 1 2) (M 2 0)),
    min (M 0 2) (min (M 1 0) (M 2 1)))

noncomputable section

/-- The finite set of normalized coefficient vectors: six nonnegative integers
bounded by `t`, summing to `t`, whose odd part `(x,y,z)` has minimum `0`. The
bound is lossless because every coordinate of such a vector is at most `t`. -/
def sm3Params (t : ℕ) : Finset (Fin 6 → Fin (t + 1)) :=
  by
    classical
    exact Finset.univ.filter fun p =>
      (∑ i : Fin 6, (p i : ℕ)) = t ∧
        min ((p 3 : ℕ)) (min ((p 4 : ℕ)) ((p 5 : ℕ))) = 0

/-- The number of normalized coefficient vectors for line sum `t`. -/
def sm3Count (t : ℕ) : ℕ := (sm3Params t).card

end

end MagicSquares
