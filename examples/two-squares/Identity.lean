/-
# Equal sums of two squares, brick 1: the four-parameter identity

We study integer solutions of `a^2 + b^2 = c^2 + d^2`.

This brick contains the purely algebraic input: the **Brahmagupta–Fibonacci**
(two-squares) product identity and the four-parameter identity it implies,

    (pr + qs)^2 + (ps - qr)^2 = (pr - qs)^2 + (ps + qr)^2.

Everything here is a polynomial identity: no ordering, no positivity, no divisibility.
The single analytic-looking consequence, the integer family of brick 2, and the
parity / gcd / completeness development live elsewhere.

## Why the identity is stated twice

`sum_two_squares_mul` and `sum_two_squares_mul'` are genuinely different statements
(the two ways of writing `(p^2+q^2)(r^2+s^2)` as a sum of two squares). The four-parameter
identity is *derived* from them rather than proved by a second `ring` call, which records
why it holds: both sides are the same product. Only the product forms need `ring`.

Scratch brick, compiled with `lake env lean`; see `missions/two-squares/status.md`.
-/

import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace TwoSquares

/-! ## The two-squares product identity -/

/-- **Brahmagupta–Fibonacci identity, first form.** Over any commutative ring,
`(p^2 + q^2)(r^2 + s^2) = (pr + qs)^2 + (ps - qr)^2`. -/
theorem sum_two_squares_mul {R : Type*} [CommRing R] (p q r s : R) :
    (p^2 + q^2) * (r^2 + s^2) = (p * r + q * s)^2 + (p * s - q * r)^2 := by
  ring

/-- **Brahmagupta–Fibonacci identity, second form.** Over any commutative ring,
`(p^2 + q^2)(r^2 + s^2) = (pr - qs)^2 + (ps + qr)^2`. -/
theorem sum_two_squares_mul' {R : Type*} [CommRing R] (p q r s : R) :
    (p^2 + q^2) * (r^2 + s^2) = (p * r - q * s)^2 + (p * s + q * r)^2 := by
  ring

/-! ## The four-parameter identity -/

/-- **Objective 1 (general form).** Over any commutative ring,
`(pr + qs)^2 + (ps - qr)^2 = (pr - qs)^2 + (ps + qr)^2`.

Both sides equal `(p^2+q^2)(r^2+s^2)`, so no ring expansion is needed here. -/
theorem four_param_identity_ring {R : Type*} [CommRing R] (p q r s : R) :
    (p * r + q * s)^2 + (p * s - q * r)^2 =
      (p * r - q * s)^2 + (p * s + q * r)^2 :=
  (sum_two_squares_mul p q r s).symm.trans (sum_two_squares_mul' p q r s)

/-- **Objective 1 (integer form).** The same identity over `ℤ`: for all integers
`p q r s`, the quadruple `(pr+qs, ps-qr, pr-qs, ps+qr)` solves `a^2+b^2 = c^2+d^2`. -/
theorem four_param_identity (p q r s : ℤ) :
    (p * r + q * s)^2 + (p * s - q * r)^2 =
      (p * r - q * s)^2 + (p * s + q * r)^2 :=
  four_param_identity_ring p q r s

/-- Read `four_param_identity` the way it is used: it *produces* a solution of
`a^2 + b^2 = c^2 + d^2` with `a = pr+qs`, `b = ps-qr`, `c = pr-qs`, `d = ps+qr`. -/
theorem four_param_gives_solution (p q r s : ℤ) :
    let a := p * r + q * s
    let b := p * s - q * r
    let c := p * r - q * s
    let d := p * s + q * r
    a^2 + b^2 = c^2 + d^2 := by
  dsimp
  exact four_param_identity p q r s

end TwoSquares
