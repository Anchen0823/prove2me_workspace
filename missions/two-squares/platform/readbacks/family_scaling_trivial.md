# Read-back: `family_scaling_trivial`

Declared in namespace `EqualTwoSquares` (file `items/family_scaling_trivial.lean`); the name agrees with the file name. Its own doc line reads *"Objective 3: no member of the family is a nontrivial integer multiple of another."*

## What the declaration literally says

Let $m, n, k \in \mathbb{Z}$ and suppose that, in $\mathbb{Z}^4$,

$$F(n) \;=\; k \cdot F(m),$$

where $F(t) = \bigl(1,\; t^2 - t + 1,\; 2t - 1,\; t^2 - t - 1\bigr)$ and $k \cdot F(m)$ denotes coordinatewise multiplication of the whole four-tuple by the integer $k$ (so the hypothesis is the conjunction of the four coordinate equalities
$1 = k\cdot 1$,
$n^2-n+1 = k\,(m^2-m+1)$,
$2n-1 = k\,(2m-1)$,
$n^2-n-1 = k\,(m^2-m-1)$). Then

$$n = m .$$

There is no assumption that $k \neq 0$, no assumption that $k \neq 1$, no assumption that the scaling is "nontrivial", and no assumption on $m, n$ other than integrality: the conclusion $n=m$ is asserted for **every** integer scalar $k$ for which the hypothesis can hold. In particular the scalar $k$ is *not* part of the conclusion; once $n = m$ is known, the first coordinate equality actually forces $k = 1$, so no member is a genuine multiple of a *different* member.

Because the first coordinate of every family member is fixed to be $1$, the first coordinate equality already reads $1 = k \cdot 1 = k$; hence the hypothesis can hold only with $k = 1$, and then any of the other coordinates (e.g. $2n-1 = 2m-1$) gives $n = m$. The hypothesis is nevertheless satisfiable — take $m = n$ arbitrary and $k = 1$ — so the theorem is not vacuous.

## Audit notes

- **Truth.** Verified: exhaustive search over $|k| \le 30$, $|m| \le 30$, $|n| \le 60$ finds no instance of the hypothesis with $n \neq m$ (in fact no instance at all with $k \neq 1$), matching the argument above. **TRUE.**
- **Faithfulness.** Name matches file name; the conclusion $n=m$ is the formal rendering of "no member is a nontrivial multiple of another" (equality of members forces equality of indices). The three variables $m, n, k$ are all implicit arguments and all appear in the hypothesis; the conclusion mentions only $m$ and $n$, which is intentional and fine. All variables are bound; nothing free.
- **Trivializing premise — flagged, but not a defect.** The hypothesis is strong enough that it essentially determines the conclusion (it forces $k = 1$ from the constant first coordinate, and then any coordinate gives $n=m$); there is no "interesting case" in which the hypothesis holds nontrivially. This is *exactly* what the item is meant to say, so it is not a logical flaw; but the reader should know that the depth of the statement is small, and that the hypothesis is satisfiable only in the "trivial" configuration $k = 1$, $n = m$. The hypothesis does not itself contain the formula $n = m$, so it does not literally restate the conclusion.
- **Satisfiability.** Satisfiable: $m = n = 0$, $k = 1$ gives $(1,1,-1,-1) = 1 \cdot (1,1,-1,-1)$. Hence non-vacuous, with infinitely many witnesses.
- **Elaboration.** Included in `statements/All.lean`; elaborates with only the expected `declaration uses 'sorry'` warning (so the scalar-multiplication notation on $\mathbb{Z}^4$ resolves: componentwise multiplication by $k$).

FAITHFUL
