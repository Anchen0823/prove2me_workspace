## Two independent small integer forms in $1$ and $\zeta(9)$

For every $\varepsilon>0$ there are integers $b_1,a_1,b_2,a_2\in\mathbb{Z}$ with

$$b_1a_2\neq b_2a_1,\qquad
\bigl|b_1+a_1\,\zeta(9)\bigr|<\varepsilon,\qquad
\bigl|b_2+a_2\,\zeta(9)\bigr|<\varepsilon,$$

where $\zeta(9)$ denotes $\operatorname{Re}\zeta(9)=
\bigl(\texttt{riemannZeta}\ (9:\mathbb{C})\bigr).\mathrm{re}$, the real value of the
Riemann zeta function at the positive integer $9$.

**Status: open.** This is the analytic obligation of the two-form route of the
mission, and it is the single child that the local mathematical DAG attaches directly
below the goal. The local notes derive it conditionally: the open target **J** (an
exponential margin $B_n+\sigma_n\le\tau-\varepsilon$ along infinitely many even $n$)
supplies, through the two-dimensional Gauss bound for the second minimum of the
inverse-image lattice, two independent integer outputs whose weighted norms are
$\le e^{(\tau-\varepsilon/2)n}$; the note-proved uniform analytic decay estimate then
gives

$$\bigl|L_n(w)\bigr|\le e^{(-\tau+o(1))n}\,\lVert w\rVert_{n,2},$$

so both integer forms $L_n(w_i)=b_i+a_i\zeta(9)$ tend to zero. Independence of the two
outputs is preserved because the inverse image $E_n$ is injective. Neither J nor the
concrete analytic decay estimate is formalised here, and neither the existence of the
forms nor their independence is asserted as proved.

**Relation to the goal.** This statement is strictly stronger than irrationality of
$\zeta(9)$: together with the two-form criterion
`ZetaNine.irrational_of_two_small_integer_forms` (already proved on this mission) it
yields the goal, which is why it is published as the goal's reduction child. It is not
equivalent to the goal, because it demands **two** non-proportional forms, which for an
irrational value is stronger than the mere existence of one approximating sequence.
