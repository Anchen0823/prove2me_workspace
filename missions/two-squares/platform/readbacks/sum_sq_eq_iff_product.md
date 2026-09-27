# Read-back: `sum_sq_eq_iff_product`

Declared in namespace `EqualTwoSquares` (file `items/sum_sq_eq_iff_product.lean`); the name agrees with the file name. Its own doc line reads *"Objective 4, rearrangement: the sum-of-squares equation rewritten as a product equation."*

## What the declaration literally says

For all integers $a, b, c, d \in \mathbb{Z}$ — with no hypotheses whatsoever — the following equivalence holds:

$$a^2 + b^2 \;=\; c^2 + d^2 \quad \Longleftrightarrow \quad (a + c)(a - c) \;=\; (d + b)(d - b) .$$

Both sides use the same four integers; the left side is the sum-of-two-squares equation, the right side the corresponding "difference-of-products" form. Explicitly, $(a+c)(a-c) = a^2 - c^2$ and $(d+b)(d-b) = d^2 - b^2$, so the right-hand equation is $a^2 - c^2 = d^2 - b^2$, which is exactly the left-hand equation with $c^2$ and $b^2$ moved across. Hence both directions of the equivalence are pure rearrangement over $\mathbb{Z}$; nothing about divisibility, parity, order or positivity is involved, and there are no hidden conditions.

The quantifiers cover every integer value: zeros (both sides then read $0 = 0$), negative entries (each square is unaffected by the sign, so both sides are unchanged under any sign flip of any variable), coincident entries (e.g. $a=c$ and $b=d$ gives $0=0$ on the right and a true equality on the left), and equal entries across the two sides.

Note what the statement does **not** say: it does not introduce the half-integers $\frac{a+c}{2}$ etc., it does not claim that $a+c$ and $a-c$ have any particular parity, and it does not assert anything equivalent to the divisibility needed later for the four-factor parametrisation — it is only the identity-level rearrangement, valid for *every* quadruple, including those for which no integral parametrisation witnesses need exist.

## Audit notes

- **Truth.** TRUE. $(a+c)(a-c) = a^2 - c^2$ and $(d+b)(d-b) = d^2 - b^2$; hence the right-hand equality is equivalent to $a^2 - c^2 = d^2 - b^2$, i.e. to $a^2 + b^2 = c^2 + d^2$. Verified exhaustively: for every quadruple with $a,b,c,d \in [-15,15]$ the truth values of the two sides agree — zero mismatches.
- **Faithfulness.** Name matches file name; the doc line "the sum-of-squares equation rewritten as a product equation" matches exactly, and the statement is an $\Longleftrightarrow$ (equivalence), not merely the forward implication, so its strength matches "rewritten as". All four variables are explicit parameters, occurring on both sides of the equivalence; nothing is free, and nothing is quantified over vacuously.
- **Trivializing premise.** None: there are no hypotheses at all, so nothing can presuppose the conclusion or render the statement vacuous.
- **Satisfiability.** No hypotheses; both sides are satisfiable and both fail for suitable choices (e.g. $a=b=c=0, d=1$ makes both sides false), so the equivalence carries real information and is not degenerate.
- **Elaboration.** Included in `statements/All.lean`; elaborates with only the expected `declaration uses 'sorry'` warning.

FAITHFUL
