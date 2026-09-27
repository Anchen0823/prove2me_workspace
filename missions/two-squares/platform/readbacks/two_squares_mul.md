# Read-back: `two_squares_mul`

Declared in namespace `EqualTwoSquares` (file `items/two_squares_mul.lean`); the name agrees with the file name. Its own doc line reads *"Brahmagupta–Fibonacci identity, both forms."*

## What the declaration literally says

Let $R$ be any type equipped with a commutative ring structure, and let $p, q, r, s \in R$. Then **both** of the following hold simultaneously (a conjunction):

$$(p^2 + q^2)\,(r^2 + s^2) \;=\; (p r + q s)^2 + (p s - q r)^2 ,$$
$$(p^2 + q^2)\,(r^2 + s^2) \;=\; (p r - q s)^2 + (p s + q r)^2 .$$

Here $x^2$ means $x \cdot x$ and the multiplication is that of the (arbitrary) commutative ring $R$; no division, ordering or integrality is used. The same value $(p^2+q^2)(r^2+s^2)$ appears on the left of both conclusions, so the two forms are two representations of one product. All four ring elements $p,q,r,s$ are explicit arguments, all occur in both conclusions, and the only implicit argument is the typeclass instance making $R$ a commutative ring.

Because the statement is completely general, it silently covers degenerate instances: rings with zero divisors, rings of positive characteristic (where $-2pqrs = 2pqrs$ may vanish, in characteristic $2$ even $2pqrs = 0$), and the zero ring; also $p=q=r=s=0$, all-equal entries, and non-units. In every one of these the identity is asserted to hold, and it does.

## Audit notes

- **Truth.** Verified by polynomial expansion: both right-hand sides expand to $p^2r^2 + p^2s^2 + q^2r^2 + q^2s^2$, which equals $(p^2+q^2)(r^2+s^2)$; no cancellation between the two sides of an equation is relied on. Additionally checked by random sampling in the (non-domain, non-reduced, mixed-characteristic) rings $\mathbb{Z}/m\mathbb{Z}$ for $m \in \{2,3,4,6,8,12,16,30\}$; no failure. **TRUE** (universally, in every commutative ring).
- **Faithfulness.** Name matches file name; doc line "both forms" matches the conjunction of the two representations. No free variables; $R$ and its ring structure are properly bound.
- **Trivializing premise.** None — there are no hypotheses beyond the typeclass `[CommRing R]`, which is a legitimate structural requirement, not an assumption of the conclusion.
- **Satisfiability.** The typeclass constraint is satisfiable (e.g. $R = \mathbb{Z}$); the quantification is non-vacuous.
- **Elaboration.** Included in `statements/All.lean`; elaborates with only the expected `declaration uses 'sorry'` warning.

FAITHFUL
