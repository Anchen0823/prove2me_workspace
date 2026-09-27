# Read-back: `explicit_family_chain`

Declared in namespace `EqualTwoSquares` (file `items/explicit_family_chain.lean`); the name agrees with the file name. Its own doc line reads *"Objective 2, inequality part: the four entries form a strict chain for every n at least 4."*

## What the declaration literally says

Let $n \in \mathbb{Z}$ satisfy the single hypothesis $4 \le n$. Then the three strict inequalities

$$1 \;<\; 2n - 1 \;<\; n^2 - n - 1 \;<\; n^2 - n + 1$$

hold jointly (a nested conjunction). The four quantities appearing are exactly the four entries of the family $(1,\; n^2-n+1,\; 2n-1,\; n^2-n-1)$ — note that they appear here re-ordered ascendingly ($1$, then $2n-1$, then $n^2-n-1$, then $n^2-n+1$), which is not the order in which they sit in the quadruple $(a,b,c,d)$. The variable $n$ is an implicit argument, constrained only by the hypothesis.

The bound $4 \le n$ is doing real work and is essentially tight: at $n = 4$ the chain reads $1 < 7 < 11 < 13$, while at $n = 3$ the middle step would read $5 < 5$, which is false. Nothing beyond this lower bound is assumed, so all $n \ge 4$ (arbitrarily large) are covered.

## Audit notes

- **Truth.** Each step checked: $1 < 2n-1$ since $2n-1 \ge 7$; $2n-1 < n^2-n-1$ is equivalent to $n^2 - 3n = n(n-3) > 0$, true for $n \ge 4$; $n^2-n-1 < n^2-n+1$ is $0 < 2$. Numerically verified for all $4 \le n \le 300$. **TRUE.**
- **Faithfulness.** Name matches file name; the doc line's "strict chain for every n at least 4" matches the stated conjunction of three strict inequalities under exactly one hypothesis $4 \le n$. All variables bound; $n$ occurs in every term of the conclusion.
- **Trivializing premise.** None: the hypothesis $4 \le n$ is a numerical bound, not a restatement of the conclusion, and is satisfiable.
- **Satisfiability.** Satisfiable and non-vacuous ($n = 4, 5, \dots$); infinitely many witnesses.
- **Elaboration.** Included in `statements/All.lean`; elaborates with only the expected `declaration uses 'sorry'` warning.

FAITHFUL
