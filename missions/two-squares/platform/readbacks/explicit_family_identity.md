# Read-back: `explicit_family_identity`

Declared in namespace `EqualTwoSquares` (file `items/explicit_family_identity.lean`); the name agrees with the file name. Its own doc line reads *"Objective 2, equality part: the explicit one-parameter family, valid for every integer n."*

## What the declaration literally says

For every integer $n \in \mathbb{Z}$, writing $A = n^2 - n$, the following equality of sums of two squares holds:

$$1^2 + (A + 1)^2 \;=\; (2n - 1)^2 + (A - 1)^2 ,$$

that is, explicitly,

$$1^2 + (n^2 - n + 1)^2 \;=\; (2n - 1)^2 + (n^2 - n - 1)^2 .$$

The single integer parameter $n$ is an explicit argument and is completely unrestricted: no positivity, no lower bound, no distinctness and no coprimality is required. The quadruple of entries involved is $(a,b,c,d) = (1,\; n^2-n+1,\; 2n-1,\; n^2-n-1)$, with $(1, n^2-n+1)$ on the left of the equality of sums of squares and $(2n-1, n^2-n-1)$ on the right.

Degenerate and edge cases silently covered: $n = 0$ gives $1^2 + 1^2 = (-1)^2 + (-1)^2$, i.e. $2 = 2$; $n = 1$ gives $1^2 + 1^2 = 1^2 + (-1)^2$; negative $n$ (e.g. $n = -1$: $1^2 + 3^2 = (-3)^2 + 1^2$, i.e. $10 = 10$); and repeated entries (for $n=0$ and $n=1$ several of the four entries coincide). The claim is asserted for all of them.

Expanding both sides confirms it: with $A = n^2-n$ the left side is $1 + (A+1)^2 = A^2 + 2A + 2$, while the right side is $(2n-1)^2 + (A-1)^2 = 4n^2-4n+1 + A^2 - 2A + 1 = A^2 - 2A + 2 + 4A = A^2 + 2A + 2$, using $4A = 4n^2 - 4n$.

## Audit notes

- **Truth.** Verified algebraically (above) and numerically for every integer $n$ with $|n| \le 300$; no counterexample. **TRUE.**
- **Faithfulness.** Name matches file name; the doc line's "valid for every integer n" corresponds exactly to the unrestricted parameter $(n : \mathbb{Z})$; the equality asserted is exactly the family identity. All variables bound.
- **Trivializing premise.** None: no hypotheses.
- **Satisfiability.** No hypothesis; instantly non-vacuous and non-trivial (e.g. $n=4$: $1^2+13^2 = 7^2+11^2 = 170$).
- **Elaboration.** Included in `statements/All.lean`; elaborates with only the expected `declaration uses 'sorry'` warning.

FAITHFUL
