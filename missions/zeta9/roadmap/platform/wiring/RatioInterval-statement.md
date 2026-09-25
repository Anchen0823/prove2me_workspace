## The weighted ratio interval contains the ratio of the sums

Let $w,a,b:\{0,1,2,3,4\}\to\mathbb{R}$ with $w_j>0$ and $b_j>0$ for every $j$, and
suppose the five ratios $a_j/b_j$ are not all equal. Then the ratio of the weighted
sums

$$\rho=\frac{\sum_j w_j\,a_j}{\sum_j w_j\,b_j}$$

is strictly between the smallest and the largest sampled ratio:

$$\exists j,\ \frac{a_j}{b_j}<\rho
\qquad\text{and}\qquad
\exists j,\ \rho<\frac{a_j}{b_j}.$$

**Why.** Write $B=\sum_j w_jb_j>0$ and reweight by $v_j=w_jb_j/B$. Then every $v_j$ is
strictly positive and $\sum_j v_j=B/B=1$, and a one-line rearrangement gives
$\rho=\sum_j v_j\,(a_j/b_j)$: the ratio of the sums is a convex combination of the
sampled ratios. The positive-weight sandwich lemma applied to $(v_j)$ and to
$r_j=a_j/b_j$ then produces the two strict inequalities.

**Scope.** This is local node **FI** in its invariant form: no normalisation is
assumed, the conclusion is about the mediant itself. The denominators $b_j$ are
strictly positive by hypothesis, so no division by a degenerate local curvature occurs,
and $B>0$ makes the mediant well-defined. The lemma is a strict-interval statement
only — it gives no quantitative separation, no exponential width, and does not decide
whether the actual changing first output lies outside the interval.
