## Positive Taylor sign forces a strictly positive kernel sum

Let $R:\mathbb{N}\to\mathbb{R}$ be a strictly positive kernel, $u:\mathbb{N}\to\mathbb{R}$
a sampling map, $p\in\mathbb{R}[X]$ a real polynomial and $u_0\in\mathbb{R}$ an
expansion point. Assume:

1. $R(k)>0$ for every $k$;
2. every sampling point lies at or beyond the expansion point, $u_0\le u(k)$;
3. every Taylor coefficient of $p$ at $u_0$ is nonnegative,
   $\bigl[\text{taylor}_{u_0}p\bigr]_i\ge 0$ for all $i$;
4. the weighted series $\sum_k R(k)\,p(u(k))$ is summable;
5. $p$ does not vanish identically on the samples, i.e. $p(u(k))>0$ for some $k$.

Then

$$\sum_{k\ge 0} R(k)\,p(u(k)) \;>\; 0 .$$

**Why.** Writing $p(u)=\sum_i (u-u_0)^i\,[\text{taylor}_{u_0}p]_i$ shows that
$p(u(k))\ge 0$ whenever $u(k)\ge u_0$ and all Taylor coefficients at $u_0$ are
nonnegative. Hence every term $R(k)\,p(u(k))$ is nonnegative, and by (5) at least one
term is strictly positive. A summable series of nonnegative terms with one strictly
positive term is strictly positive.

The analogous statement with all Taylor coefficients nonpositive, concluded as
$\sum_k R(k)p(u(k))<0$, follows by applying the theorem to $-p$.

**Scope.** This is the *positive-kernel* half of local node **TP**. On the actual
construction the sampling points are $u(k)=k(k+n)$ with $u(k)\ge(n+1)(2n+1)=:u_0$
for $k>n$, so hypothesis (2) is the note's observation that the whole summation tail
lies beyond the expansion point, and hypothesis (3) is the weak one-sign Taylor
condition that the open targets T, TG, TS, T5 are supposed to supply along infinitely
many even $n$. The theorem does not assert that any such sign condition holds for the
actual moving shortest vectors; it only rules out a vanishing sum once a sign is
given. Hypothesis (4) is a genuine summability input and is not automatic.
