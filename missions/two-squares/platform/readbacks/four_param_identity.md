# Read-back: `four_param_identity`

Declared in namespace `EqualTwoSquares` (file `items/four_param_identity.lean`); the name agrees with the file name. Its own doc line reads *"Objective 1: the four-parameter identity over the integers."*

## What the declaration literally says

For all integers $p, q, r, s \in \mathbb{Z}$,

$$(p r + q s)^2 + (p s - q r)^2 \;=\; (p r - q s)^2 + (p s + q r)^2 .$$

There are no hypotheses and no hidden parameters: the four letters are explicit arguments of type integer, and every one of them occurs in the displayed identity. Nothing is vacuous, nothing is degenerate: the claim is asserted for *all* integer choices, including the all-zero choice $p=q=r=s=0$ (both sides $=0$), the cases where some parameters are equal, and negative values of the parameters (where the identity still holds because the cross terms cancel with opposite signs).

Expanding both sides explains the content: the left-hand side expands to
$p^2r^2 + 2pqrs + q^2s^2 + p^2s^2 - 2pqrs + q^2r^2 = p^2r^2 + p^2s^2 + q^2r^2 + q^2s^2$, and the right-hand side expands to
$p^2r^2 - 2pqrs + q^2s^2 + p^2s^2 + 2pqrs + q^2r^2$, i.e. to the same quantity.

## Audit notes

- **Truth.** Verified: the two sides are the same polynomial in $\mathbb{Z}[p,q,r,s]$; the cross terms $+2pqrs$ and $-2pqrs$ cancel on each side independently, so the identity does not even need cancellation between the sides. Checked symbolically and numerically over a large random range of parameters. **TRUE.**
- **Faithfulness.** Name matches file name. The statement says exactly what its doc line claims — a polynomial identity in four integer parameters. No variables occur free.
- **Trivializing premise.** None: the theorem has no hypotheses at all.
- **Satisfiability.** No hypothesis to satisfy; the universal claim is non-vacuously instantiated (e.g. $p=q=r=s=1$ gives $2^2+0^2 = 0^2+2^2$).
- **Elaboration.** Included in `statements/All.lean`; elaborates with only the expected `declaration uses 'sorry'` warning.

*Remark for the human auditor:* the statement is over $\mathbb{Z}$ only; it is a special case of the corresponding identity in any commutative ring (cf. `two_squares_mul`), and unlike `two_squares_mul` it does **not** assert the product form $(p^2+q^2)(r^2+s^2)$. If the intent was to capture the Brahmagupta–Fibonacci product, this statement alone does not say it. That is a matter of coverage, not incorrectness: the statement is complete and correct as written.

FAITHFUL
