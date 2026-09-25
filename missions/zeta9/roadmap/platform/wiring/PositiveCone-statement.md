## An entrywise positive matrix maps the nonnegative cone into the positive cone

Let $M$ be a real $5\times5$ matrix whose entries are all strictly positive, and let
$v\in\mathbb{R}^5$ be a nonzero vector with $v_i\ge0$ for every $i$. Then the product
$Mv$ has every coordinate strictly positive:

$$\forall i,\ 0<(Mv)_i .$$

**Why.** $(Mv)_i=\sum_j M_{ij}v_j$. Each summand is nonnegative, because $M_{ij}>0$ and
$v_j\ge0$. Since $v\ne0$ and $v\ge0$ there is an index $j_0$ with $v_{j_0}>0$, and then
$M_{ij_0}v_{j_0}>0$ for **every** row $i$. A finite sum of nonnegative reals with one
strictly positive term is strictly positive.

**Scope.** This is the positive-cone step of local node **TA**. The note's point is
that the one-step Taylor transfer has mixed signs, so it does not preserve the cone,
while the two-step transfer $H_nH_{n+2}$ is eventually strictly entrywise positive and
therefore does. This lemma isolates that step: it shows that once a transfer matrix is
strictly positive, a coefficient vector that is already weakly one-signed and nonzero
becomes strictly one-signed. It does **not** by itself conclude that a fixed output's
Taylor coefficients share the sign of its real value — that identification needs the
limit/Perron argument and the positive-moment column, which are not formalised here —
and it says nothing about a uniform entry time for outputs that move with $n$.
