# Reduction: a five-sample one-sign test forces non-vanishing

This submission reduces the five-sample non-vanishing certificate to **one** child,
`ZetaNine.quadrature_exact_of_moments` (already Proved on this mission), and proves the
rest directly.

**Statement proved.** For a real linear functional $L$ on $\mathbb{R}[X]$, five
distinct nodes $y$, five strictly positive weights $w$, and moment agreement
$L(X^m)=\sum_jw_jy_j^m$ for $0\le m\le4$: every nonzero polynomial of degree at most
four whose five sampled values are weakly of one sign satisfies $L(p)\ne0$.

**Argument.** The child gives $L(p)=\sum_j w_j\,p(y_j)$ — this is the moment-matching
step, and importing it is the whole point of this reduction. Each summand then has the
sign required at its node. If $L(p)=0$, a sum of identically signed terms equal to zero
forces each summand to be zero (`Finset.sum_eq_zero_iff_of_nonneg`, applied directly in
the nonnegative case and to the negated sum in the nonpositive case). Since every
weight is nonzero, $p(y_j)=0$ at all five nodes. A nonzero polynomial of degree at most
four cannot have five distinct roots
(`Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero`), which contradicts
non-vanishing.

**What the child does and does not give.** The imported theorem is a general statement
about an abstract linear functional; it contains no information about $\zeta(9)$. All
the domain-specific content of this node is on the *outside*: it is what turns the
five-sample sign test of local node FQ into the non-vanishing half of local node TP.
No hypothesis is assumed that the source does not have: distinctness of the nodes,
strict positivity of the weights (needed for the import to be applicable and for the
weak-to-strict conversion) and degree at most four are all part of the note's setting,
and the negative sign case is covered by a disjunctive hypothesis rather than a
separate theorem.

**Scope.** The statement is deliberately weaker than any concrete claim: it does not
say that the actual cubature weights are positive, and it does not say that the actual
shortest output passes the test. It only certifies non-vanishing *conditional* on a
weak one-sign pattern at five distinct nodes.
