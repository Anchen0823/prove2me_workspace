# Proof: exact quadrature on quartics from the first five moments

The submission proves that if a linear functional $L$ on $\mathbb R[X]$ and a
five-node rule with nodes $y_j$ and weights $w_j$ agree on the first five moments,

$$L(X^m)=\sum_{j=0}^{4} w_j y_j^m \qquad (0\le m\le 4),$$

then they agree on every polynomial of degree at most four:
$L(p)=\sum_j w_j\,p(y_j)$.

**Argument.** Degree $\le 4$ means $p$ is a linear combination of
$1,X,X^2,X^3,X^4$. Both sides are $\mathbb R$-linear in $p$; they agree on each
monomial by hypothesis, hence on all their linear combinations.

**Formal steps.** `Polynomial.as_sum_range_C_mul_X_pow'` rewrites $p$ as
$\sum_{i<5}[\mathrm{coeff}_i\,p]\,X^i$. Applying $L$ and using its additivity and
$\mathbb R$-homogeneity turns $L(p)$ into
$\sum_{i<5}[\mathrm{coeff}_i\,p]\cdot L(X^i)$. On the other side,
`Polynomial.eval_eq_sum_range'` expands each $p(y_j)$, `Finset.mul_sum` and
`Finset.sum_comm` exchange the two finite sums into the same coefficient-weighted
shape, and the moment hypothesis identifies $L(X^i)$ with $\sum_j w_j y_j^i$ for the
five indices $i<5$.

**Scope.** This is the exact algebraic core of local node FQ. In the concrete
construction $L$ is the complete infinite positive-kernel sum restricted to
quartics and the five nodes are the prescribed integers
$k_{n,j}=\lfloor nx_*+j\sqrt{n/a}+1/2\rfloor$, with weights solving the corresponding
Vandermonde system; because the saddle coordinate is affine in $k(k+n)/n^2$, a
quartic in the kernel variable is a quartic here, which is what lets degree four
suffice. The theorem does **not** prove that the actual weights are strictly
positive — that is the analytic Gaussian-moment input — and it does not prove the
open infinite five-sample sign assertion T5.
