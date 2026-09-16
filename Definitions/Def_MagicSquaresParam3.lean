import Mathlib
import Definitions.Def_MagicSquares

set_option autoImplicit false

/-!
# Magic squares of order three: the MacMahon parametrization

This module sets up the classical parametrization of $3 \times 3$ magic squares
that underlies MacMahon's count
$$M_{3}(3e) = 2e^{2} + 2e + 1 .$$

Let $M$ be a $3 \times 3$ magic square with nonnegative integer entries and line
sum $s = 3e$. By `center_of_order_three` the centre is $e$. Putting
$a = M_{00}$ and $c = M_{02}$ and chasing the eight line identities gives

$$M \;=\; \begin{pmatrix}
a & 3e-a-c & c \\
e+c-a & e & e+a-c \\
2e-c & a+c-e & 2e-a
\end{pmatrix}$$

so the square is completely determined by the pair $(a, c)$. All nine entries are
nonnegative exactly when

$$e \le a + c \le 3e, \qquad a \le e + c, \qquad c \le e + a,$$

and these inequalities in turn force $0 \le a, c \le 2e$ (add $a + c \le 3e$ to
$a \le e + c$ to get $2a \le 4e$, and symmetrically). Writing $p = a - e$ and
$q = c - e$, the four inequalities say $|p+q| \le e$ and $|p-q| \le e$, i.e.
$|p| + |q| \le e$; so the parameter set is in bijection with the $\ell_{1}$ ball
of radius $e$ in $\mathbb{Z}^{2}$, which contains
$1 + 4\sum_{k=1}^{e} k = 2e^{2} + 2e + 1$ lattice points.

The module provides the parametrization `mkMagic3`, the finite parameter set
`paramSet`, and the counting function `paramCount`. The two substantive
statements — that `mkMagic3` sets up a bijection onto the magic squares, and that
`paramCount e = 2e^2 + 2e + 1` — are submitted separately as theorems.
-/

namespace MagicSquares

/-- The canonical $3 \times 3$ array attached to a line sum `3 * e` and two
parameters `a`, `c`, as in the module docstring. Entries are natural numbers, so
the subtractions are truncated; the row/column/diagonal identities hold under the
admissibility inequalities recorded in `paramSet`. -/
def mkMagic3 (e a c : ℕ) : Square 3 ℕ :=
  ![![a, 3 * e - a - c, c],
    ![e + c - a, e, e + a - c],
    ![2 * e - c, a + c - e, 2 * e - a]]

noncomputable section

/-- Whether a parameter pair `(a, c)` is admissible for line sum `3 * e`. -/
def IsParam3 (e a c : ℕ) : Prop :=
  e ≤ a + c ∧ a + c ≤ 3 * e ∧ a ≤ e + c ∧ c ≤ e + a

/-- The finite set of admissible parameter pairs. As shown in the module
docstring, admissibility forces `a ≤ 2 * e` and `c ≤ 2 * e`, so searching the
`[0, 2e] × [0, 2e]` box is lossless. -/
def paramSet (e : ℕ) : Finset (ℕ × ℕ) :=
  by
    classical
    exact ((Finset.range (2 * e + 1)).product (Finset.range (2 * e + 1))).filter
      (fun ac => IsParam3 e ac.1 ac.2)

/-- The number of admissible parameter pairs for line sum `3 * e`. -/
def paramCount (e : ℕ) : ℕ := (paramSet e).card

end

end MagicSquares
