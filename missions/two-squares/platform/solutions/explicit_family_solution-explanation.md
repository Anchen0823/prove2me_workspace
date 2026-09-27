# Proof: the family produces a nontrivial solution

For every integer $n\ge4$ the quadruple $(1,\;n^2-n+1,\;2n-1,\;n^2-n-1)$ satisfies
$a^2+b^2=c^2+d^2$, all four entries are positive, and all six pairs are distinct.

**Argument.** The proof is assembled from one equality and three inequalities:

1. The equality is a polynomial identity, closed by `ring`.
2. The three inequalities $1<2n-1$, $2n-1<n^2-n-1$, $n^2-n-1<n^2-n+1$ come from `nlinarith`
   using $4\le n$ (the middle one is $n(n-3)>0$).
3. Composing them with `lt_trans` gives $1<n^2-n-1$, $1<n^2-n+1$ and $2n-1<n^2-n+1$, so the
   three remaining pairs are ordered too; `ne_of_lt` turns all six orderings into the six
   required disequalities. Positivity follows from the chain together with $0<1$.

**What is and is not claimed.** This is a *witness* of nontriviality, not a classification:
it exhibits infinitely many genuinely distinct solutions but says nothing about how a given
solution arises. The classification direction is the goal of the mission and is not used here.

**Boundary.** The threshold $n\ge4$ is sharp: at $n=3$ the entries $2n-1$ and $n^2-n-1$ are
both $5$, so the distinctness conclusion genuinely fails below $4$.
