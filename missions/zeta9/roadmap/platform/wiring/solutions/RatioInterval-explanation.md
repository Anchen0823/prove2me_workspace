# Reduction: the weighted ratio interval contains the ratio of the sums

This submission reduces the weighted-mediant statement to **one** child, the
positive-weight sandwich `ZetaNine.min_lt_weighted_average_lt_max`, and proves the
reweighting directly.

**Statement proved.** With $w_j>0$, $b_j>0$ and five not-all-equal ratios $a_j/b_j$,
the mediant $\rho=\bigl(\sum_jw_ja_j\bigr)/\bigl(\sum_jw_jb_j\bigr)$ is strictly above
one sampled ratio and strictly below another.

**Argument.** Put $B=\sum_jw_jb_j>0$ and define the reweighted vector
$v_j=w_jb_j/B$. Then $v_j>0$ and $\sum_jv_j=B/B=1$, so $v$ is an admissible weight
vector for the child. A direct rearrangement shows
$\rho=\sum_j v_j\,(a_j/b_j)$: multiplying the right-hand side by $B$ recovers
$\sum_jw_ja_j$. The child applied to $(v_j)$ and $r_j=a_j/b_j$ gives the two strict
inequalities.

**Why the reweighting is the whole content.** The mediant is a *fixed* expression;
the only work is to recognise it as a convex combination of the sampled ratios. That is
why the proof is short, and why this is a genuine reduction rather than a restatement:
the child is the general sandwich lemma, stated for arbitrary positive weights summing
to one and an arbitrary non-constant vector, and it has no arithmetic content. The
imported child is closed (a proposition about arbitrary data), so no parameterised
schema is being smuggled in.

**Scope.** Strict positivity of the $b_j$ is a hypothesis, so no division by a
vanishing local curvature is hidden; the positivity of $B$ is derived rather than
assumed. Non-equality of the ratios is exactly the non-degeneracy that the
construction supplies from the rank-two inverse image. The node is an ordering
statement only: no width, no exponent, and no assertion about the moving first output.
