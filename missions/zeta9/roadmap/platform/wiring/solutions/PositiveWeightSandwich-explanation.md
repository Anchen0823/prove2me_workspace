# Proof: positive weights sandwich their weighted average

The submission proves that if $w_j>0$ for all five indices, $\sum_jw_j=1$ and the
vector $r$ is not constant, then the weighted average $S=\sum_jw_jr_j$ satisfies
$\exists j,\ r_j<S$ and $\exists j,\ S<r_j$.

**Argument.** The proof isolates one quantitative fact: *a nonnegative combination of
nonnegative terms that sums to zero has every term zero.* Two instances of it give both
inequalities.

For the lower inequality, suppose instead that $S\le r_j$ for every $j$. Then
$w_j(r_j-S)\ge0$ for every $j$, and
$\sum_j w_j(r_j-S)=S-(\sum_jw_j)S=S-S=0$. Each summand is therefore zero, and since
$w_j\ne0$ this gives $r_j=S$ for every $j$, contradicting non-constancy of $r$. The
upper inequality is the same computation for $\sum_j w_j(S-r_j)$.

**Implementation notes.** The zero-sum step uses
`Finset.sum_eq_zero_iff_of_nonneg`, the factorisations use `Finset.sum_sub_distrib` and
`Finset.sum_mul`, and negation is handled without any `push_neg`-style rewriting: from
the contradictory hypothesis one obtains $c\le r_i$ by `not_lt.mp`, so the two helpers
share one shape. No ordering of the index set, compactness, or choice of an extremal
index is used — the argument is purely about sums.

**Scope.** This is the ordering step of local node FI. It says nothing about the width
of the interval, its exponential contraction, or whether the actual moving first output
avoids it; the non-constancy hypothesis is the abstract counterpart of the rank-two
non-degeneracy of the inverse image, and it is a genuine hypothesis, not a formality —
for constant $r$ the conclusion is false ($S=r_j$ for every $j$).
