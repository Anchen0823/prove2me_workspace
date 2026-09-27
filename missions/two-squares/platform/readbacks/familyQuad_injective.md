# Read-back: `familyQuad_injective`

Declared in namespace `EqualTwoSquares` (file `items/familyQuad_injective.lean`); the name agrees with the file name. Its own doc line reads *"Objective 3: the parametrisation n ↦ (1, n^2-n+1, 2n-1, n^2-n-1) is injective."*

## What the declaration literally says

The map

$$F : \mathbb{Z} \longrightarrow \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z} \times \mathbb{Z}, \qquad F(n) = \bigl(1,\; n^2 - n + 1,\; 2n - 1,\; n^2 - n - 1\bigr)$$

is injective: for all integers $n_1, n_2$, if $F(n_1) = F(n_2)$ then $n_1 = n_2$. Equality here is equality of the whole four-tuple, i.e. equality in each of the four coordinates simultaneously; unequal indices are claimed to produce unequal tuples, and no hypothesis restricts the indices.

Note what this does *not* say: nothing about the images being distinct as unordered sets, nothing about surjectivity, nothing about injectivity up to the symmetry $(a,b,c,d) \mapsto (c,d,a,b)$ or other reorderings, and nothing about $n$ being positive or bounded. Degenerate values are silently included: $n = 0$ gives $(1,1,-1,-1)$ and $n = 1$ gives $(1,1,1,-1)$, distinct tuples, so no collision arises even there.

Injectivity is witnessed already by the third coordinate alone: $2n-1 = 2n_2-1$ forces $n_1 = n_2$ in $\mathbb{Z}$.

## Audit notes

- **Truth.** Verified exhaustively: $F(n)$ computed for every $n$ with $|n| \le 2000$ produces no repeated tuple; algebraically, coordinate 3 gives $2n_1 - 1 = 2n_2 - 1 \Rightarrow n_1 = n_2$. **TRUE.**
- **Faithfulness.** Name matches file name, and the doc line's parametrisation $n \mapsto (1, n^2-n+1, 2n-1, n^2-n-1)$ is exactly the map whose injectivity is asserted. Every variable is bound by the statement itself (the two indices are the hidden arguments of the injectivity quantifier); nothing free.
- **Trivializing premise.** None: there are no hypotheses. Every map either is or is not injective; no assumption smuggles in the conclusion.
- **Satisfiability.** No hypothesis to satisfy; the domain $\mathbb{Z}$ is non-empty, so the statement is non-vacuous, and its content is genuinely realised (different indices do give different tuples, e.g. $n=0$ vs $n=1$).
- **Elaboration.** Included in `statements/All.lean`; elaborates with only the expected `declaration uses 'sorry'` warning.

FAITHFUL
