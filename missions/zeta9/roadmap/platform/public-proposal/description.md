## Motivation

A standard way to prove that a real number $\alpha$ is **irrational** is to produce integer
linear forms $b+a\alpha$ that are nonzero but arbitrarily small: if $\alpha=p/q$ were
rational, then $bq+ap$ would be a nonzero integer of absolute value below $1$ once the form
is smaller than $1/q$. This is the shape of every hypergeometric construction of linear
forms in odd zeta values — Rivoal's proof that infinitely many $\zeta(2n+1)$ are irrational
and Zudilin's proof that at least one of $\zeta(5),\zeta(7),\zeta(9),\zeta(11)$ is
irrational both produce such forms and read off irrationality (of at least one member of a
finite set) from a determinant condition.

The same reduction is useful in the other direction: it isolates exactly what a
construction has to supply — small forms — from the arithmetic that consumes them. This
mission formalizes that **abstract layer**: the criteria that turn small integer forms into
irrationality, together with the positivity and quadrature lemmas used to certify that a
form is nonzero.

The material is distilled from a research note on $\zeta(9)$ (Xu, 2026). That note does
**not** prove the irrationality of $\zeta(9)$, and nothing in this mission depends on
whether it can be: every statement below is a statement about real numbers, integer linear
forms, real polynomials, and finite sums, with $\zeta(9)$ and every other specific constant
removed.

## Setting

All objects live over $\mathbb{R}$.

* An **integer linear form** in $x$ is a number $b+a\,x$ with $a,b\in\mathbb{Z}$; the pair
  $(b,a)$ is its coefficient vector. Two forms are **independent** when their coefficient
  vectors have nonzero cross determinant, $b_1a_2\neq b_2a_1$.
* `Irrational x` is Mathlib's predicate: $x\notin\mathbb{Q}$ as a real number.
* The **moment-matching** hypothesis for a linear functional $L$ on real polynomials, a
  five-point node vector $y$ and a weight vector $w$, is
  $L(X^m)=\sum_{j}w_j\,y_j^{\,m}$ for every $m\le 4$. A functional satisfying it is
  **exact** on a polynomial $p$ when $L\,p=\sum_j w_j\,p(y_j)$.
* A **positive weight vector** has $w_j>0$ for all $j$; a node vector is **injective** when
  $y$ is injective on `Fin 5`.
* `Polynomial.taylor u₀ p` is the Taylor expansion of $p$ about $u_0$; its **coefficients
  are nonnegative** when $($`taylor u₀ p`$).\mathrm{coeff}\ i\ge 0$ for every $i$.
* `Matrix.mulVec M v` is the usual matrix–vector product over `Fin 5`; $\sum'$ denotes
  `tsum` over a `Summable` family.

## Formalization targets

### Goal — the one-form criterion

$$ \bigl(\forall \varepsilon>0,\ \exists\, b,a\in\mathbb{Z}:\ b+ax\neq 0\ \wedge\ |b+ax|<\varepsilon\bigr)\ \Longrightarrow\ \text{$x$ irrational.} $$

The goal is the weakest non-vacuous statement in the family: it assumes one form at a
time and no rate.

### Stronger — the two-form criterion

$$ \bigl(\forall \varepsilon>0,\ \exists\, b_1a_1b_2a_2\in\mathbb{Z}:\ b_1a_2\neq b_2a_1\ \wedge\ |b_1+a_1x|<\varepsilon\ \wedge\ |b_2+a_2x|<\varepsilon\bigr)\ \Longrightarrow\ \text{$x$ irrational.} $$

### Supporting targets

1. **Moment-matching quadrature** — matching the five moments $m\le 4$ implies exactness on
   every polynomial of degree at most $4$.
2. **Weighted average is interior** — with positive weights summing to $1$, a non-constant
   five-tuple has its weighted average strictly between its minimum and maximum.
3. **Mediant is interior** — the ratio $\sum w_ia_i\,/\,\sum w_ib_i$ with $w,b>0$ lies
   strictly between the extreme values of $a_j/b_j$.
4. **Positive matrices** — an entrywise positive $5\times5$ matrix sends every nonzero
   nonnegative vector to a strictly positive vector.
5. **Taylor-sign kernel sum** — nonnegative Taylor coefficients at a lower bound of a
   sequence, positive summable weights, and one positive sample force a strictly positive
   weighted sum.
6. **Five-sample nonvanishing** — under moment matching with positive weights and injective
   nodes, a nonzero polynomial of degree $\le 4$ whose five sampled values share a sign has
   $L\,p\neq 0$.

Targets 1–6 correspond to the mission's milestones; the goal and the two-form criterion
close the mission.

## Significance

*The results.* The two criteria are the exact statements that a linear-form construction
has to feed, and they are what turns "small forms exist" into irrationality without any
analytic input. The supporting lemmas are the standard certificates used to show a form is
*nonzero* — which is the other half of the argument, and the half that finite checks can
actually settle.

*Formalizing them.* All eight statements are elementary and already have informal proofs;
each also has a locally compiled Lean proof (`lake env lean`, exit 0, no `sorry`) against
Lean 4.33.1 and Mathlib revision `0df444a3`, held by the mission captain and published in
the companion repository. What this mission adds is platform verification plus reusable
infrastructure: the moment-matching quadrature lemma, the weighted-average and mediant
inequalities, and the positivity lemmas are stated in a form that transfers to any setting
where five-point data is certified by moments. Alternative proofs, generalizations to
$n$-point quadrature, and sharper variants are welcome contributions.

## Difficulty

*The integrality step, not the estimate.* In the one-form criterion the obvious move —
take $\varepsilon=1/|q|$ — leaves the real inequality $|b+ax|<1/|q|$, which says nothing
until the form is rewritten as $(bq+ap)/q$ with $bq+ap\in\mathbb{Z}$; only then does
$|\,\cdot\,|<1$ force vanishing and contradict nonzeroness. Writing that rewrite in Lean
means carrying the cast from $\mathbb{Z}$ through `field_simp` and back through
`exact_mod_cast`, which is where naive attempts break.

*Moment matching needs a degree bound, not interpolation.* The quadrature lemma is not
"five values determine a degree-$4$ polynomial": the hypothesis is about the functional
$L$ on the five monomials, and the proof must expand an arbitrary $p$ in the monomial
basis (`as_sum_range_C_mul_X_pow'` with `natDegree < 5`) and commute two finite sums.

*Sign conditions are load-bearing.* In target 6, the shared-sign hypothesis is what turns a
vanishing weighted sum into vanishing samples; the root-counting step then needs injective
nodes and positive weights. Dropping either silently makes the statement false, and both
are easy to forget.

## Formalization scope

Everything is over $\mathbb{R}$; no complex numbers appear. The quadrature statements are
fixed at five nodes (`Fin 5`) and degree $\le 4$, as in the source note; the functional $L$
is a `Polynomial ℝ →ₗ[ℝ] ℝ`, not a measure. `natDegree` (not `degree`) is the degree
notion. The infinite sum in target 5 is `tsum` with an explicit `Summable` hypothesis.
Matrices are `Matrix (Fin 5) (Fin 5) ℝ` with `mulVec`; irrationality is Mathlib's
`Irrational`.

*Ruled out:* a quadrature statement in which the weights are unconstrained by positivity
but the conclusion is strengthened to a lower bound — target 1 assumes only moment
matching, and any strengthening must add hypotheses rather than reinterpret the existing
ones. A "criterion" whose hypothesis is vacuous for every real $x$ is likewise out of
scope: both criteria are satisfiable hypotheses, not vacuous ones.

Infrastructure needed: the polynomial expansion and evaluation lemmas (`as_sum_range`,
`eval_eq_sum_range'`), `Finset` sum rearrangement, `Matrix.mulVec`, `Summable.tsum_lt_tsum_of_nonneg`,
and `irrational_iff_ne_rational`. The quadrature lemma, the mediant inequality, and the
positivity lemmas are reusable beyond this mission.

## Selected references

- Y. Xu, *Research Notes on ζ(9): Constructions, Computations, and Open Problems*, v0.1,
  Zenodo, 2026. <https://doi.org/10.5281/zenodo.22951155>
- W. Zudilin, *Arithmetic of linear forms involving odd zeta values*, J. Théor. Nombres
  Bordeaux 16:1 (2004), 251–291. <https://arxiv.org/abs/math/0206176>
- T. Rivoal, *La fonction zêta de Riemann prend une infinité de valeurs irrationnelles aux
  entiers impairs*, C. R. Acad. Sci. Paris Sér. I Math. 331 (2000), 267–270.
  <https://arxiv.org/abs/math/0008051>
