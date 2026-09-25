# Proof: positive Taylor sign forces a strictly positive kernel sum

The submission proves that for a strictly positive kernel $R$, sampling map $u$,
polynomial $p$ and expansion point $u_0$, if

* $R(k)>0$ for all $k$,
* $u_0\le u(k)$ for all $k$,
* every Taylor coefficient of $p$ at $u_0$ is $\ge 0$,
* $\sum_k R(k)p(u(k))$ is summable, and
* $p(u(k))>0$ for at least one $k$,

then $\sum_k R(k)p(u(k))>0$.

**Argument.** By the defining property of `Polynomial.taylor`,
$(p.\text{taylor}_{u_0}).\mathrm{eval}\,(u(k)-u_0)=p.\mathrm{eval}\,u(k)$. Since
$u(k)-u_0\ge 0$ and all coefficients of $\text{taylor}_{u_0}p$ are nonnegative, the
monomial expansion `Polynomial.eval_eq_sum_range` expresses $p(u(k))$ as a sum of
nonnegative terms, so $p(u(k))\ge 0$ for every $k$. Every summand
$R(k)\,p(u(k))$ is therefore nonnegative, and the fifth hypothesis makes one of them
strictly positive. A summable series of nonnegative real terms with one strictly
positive term is strictly positive, which is the strict comparison instance
`Summable.tsum_lt_tsum_of_nonneg` against the zero series.

The negative version — all Taylor coefficients $\le 0$ forces a strictly negative
sum — follows by replacing $p$ with $-p$.

**Scope.** This is the positive-kernel half of local node TP. It is a general
statement about an abstract positive kernel and an abstract sampling map; it does
not assert that any concrete moving first output of the $\zeta(9)$ construction
carries such a sign, which is what the open targets T, TG, TS and T5 would supply.
Summability is a genuine hypothesis, not a formality.
