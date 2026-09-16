import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresParam3
import Theorems.Thm_MagicSquares_magic_three_param_bij
import Theorems.Thm_MagicSquares_param_three_card

set_option autoImplicit false

open MagicSquares

/-- Reduction of `MagicSquares.magic_count_three_divisible`.

MacMahon's count $M_3(3e) = 2e^2 + 2e + 1$ splits into the two imported children:

* `magic_three_param_bij` — the map `M \u21a6 (M 0 0, M 0 2)` is a bijection from
  the $3 \times 3$ magic squares of line sum $3e$ onto the admissible parameter
  pairs, so `magicCount 3 (3 * e) = paramCount e`;
* `param_three_card` — the admissible pairs are in bijection with the
  $\ell_1$ ball $\{(p,q) \in \mathbb{Z}^2 : |p| + |q| \le e\}$, which has
  $1 + 4\sum_{k=1}^{e} k = 2e^2 + 2e + 1$ points.

Composing the two identities gives the theorem. -/
theorem solution (e : ℕ) : magicCount 3 (3 * e) = 2 * e ^ 2 + 2 * e + 1 := by
  rw [magic_three_param_bij e, param_three_card e]
