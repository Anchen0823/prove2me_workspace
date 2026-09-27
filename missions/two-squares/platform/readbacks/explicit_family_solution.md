# Read-back: `explicit_family_solution`

Declared in namespace `EqualTwoSquares` (file `items/explicit_family_solution.lean`); the name agrees with the file name. Its own doc line reads *"Objective 2 assembled: a positive solution with four pairwise distinct entries."*

## What the declaration literally says

Let $n \in \mathbb{Z}$ satisfy $4 \le n$. Put

$$a = 1,\qquad b = n^2 - n + 1,\qquad c = 2n - 1,\qquad d = n^2 - n - 1 .$$

Then the following three things hold jointly:

1. **The equation:** $a^2 + b^2 = c^2 + d^2$, i.e. $1^2 + (n^2-n+1)^2 = (2n-1)^2 + (n^2-n-1)^2$;
2. **Positivity of all four entries:** $0 < 1$, $0 < n^2-n+1$, $0 < 2n-1$, and $0 < n^2-n-1$;
3. **Pairwise distinctness:** all six pairwise disequalities among the four entries hold, namely
   $1 \neq 2n-1$, $1 \neq n^2-n-1$, $1 \neq n^2-n+1$, $2n-1 \neq n^2-n-1$, $2n-1 \neq n^2-n+1$, $n^2-n-1 \neq n^2-n+1$.

Unlike the sibling item `explicit_family_chain`, this statement does **not** assert any ordering of the four entries — only that no two of them are equal. The lower bound $4 \le n$ is the only hypothesis; it is genuinely needed (at $n = 3$ one gets $2n-1 = 5 = n^2-n-1$, so distinctness fails, and at $n \in \{0,1\}$ positivity/distinctness fail as well).

## Audit notes

- **Truth.** All nine listed conjuncts verified for every $4 \le n \le 300$ by direct evaluation, and justified symbolically: positivity is clear from $2n-1 \ge 7$, $n^2-n-1 \ge 11$, $n^2-n+1 \ge 13$; distinctness reduces to $n(n-3) \neq 0$, $(n-1)(n-2) \neq 0$ and the constant gap $2$ between $n^2-n-1$ and $n^2-n+1$, all valid for $n \ge 4$. **TRUE.**
- **Faithfulness.** Name matches file name. The doc line claims "a positive solution with four pairwise distinct entries", and the statement delivers exactly: the family identity, strict positivity of each of the four entries, and *all six* pairwise disequalities (complete pairwise distinctness, not a partial list). Variables: only $n$, implicit, constrained by the hypothesis and occurring throughout; nothing free.
- **Trivializing premise.** None: $4 \le n$ is a pure numerical bound and is not the conclusion nor a contradiction.
- **Satisfiability.** Satisfiable with plenty of witnesses ($n = 4$ already gives the entry set $\{1, 7, 11, 13\}$ and the equality $170 = 170$); non-vacuous.
- **Elaboration.** Included in `statements/All.lean`; elaborates with only the expected `declaration uses 'sorry'` warning.

FAITHFUL
