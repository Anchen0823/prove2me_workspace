This submission proves Corollary 3.5 **at the sharp block count** — a range of
odd integers of width $2q$ costs one block rather than two — from the corrected
single-block estimate of Lemma 3.4. The analytic content sits entirely in the
child; what happens here is the reindexing, and it is exactly the reindexing
that fixes the constant.

## Statement

Let $q\ge1$, $A\ge0$, $B\ge0$, let $a'$ be coprime to $q$, and let
$2\alpha=\frac{a'}q+\beta$ with $|\beta|\le q^{-2}$. Then for all real $\theta$
and all $x<y$ with $y-x\le 2q$,

$$\sum_{\substack{z\in(x,y]_{\mathbb Z}\\ z\ \mathrm{odd}}}\ \mathrm{vmin}(A,B,\alpha,\theta;z)\ \le\ 2A+\frac2\pi Bq\log 4q .$$

## The one observation

Write $z=2m+1$. Then

$$\pi\alpha(2m+1)+\theta=\pi(2\alpha)m+(\pi\alpha+\theta),$$

so the *odd* sum over $z\in(x,y]$ with frequency $\alpha$ and phase $\theta$ **is**
the *full* sum over $m\in\bigl(\frac{x-1}2,\frac{y-1}2\bigr]$ with frequency
$2\alpha$ and phase $\pi\alpha+\theta$. The $m$-range has width $\frac{y-x}2$, so
as soon as $y-x\le2q$ it has width at most $q$ — precisely the hypothesis under
which the block estimate applies once.

Two things happen simultaneously and are the same phenomenon seen from two
sides: the admissible width doubles, and the frequency doubles. This is why the
hypothesis of the statement is $2\alpha=\frac{a'}q+\beta$ (the source's
hypothesis for Corollary 3.5) rather than $\alpha=\frac aq+\beta$.

## Why the count is one and not two

The published Corollary 3.5 carries the covering count
$\bigl\lfloor\frac{y-x}{2q}\bigr\rfloor+1$. On the blocks of Section 5.2,
$2jq+\frac q2<d\le2(j+1)q+\frac q2$, the width is exactly $2q$, so that count is
$\lfloor1\rfloor+1=2$. But $\lfloor W/L\rfloor+1$ is the number of length-$L$
blocks needed to cover a range of width $W$ only when $L\nmid W$; in general the
count is $\lceil W/L\rceil$, and the two differ by one exactly when $L\mid W$.
Here $L=2q$ and $W=2q$, so the count is $1$.

This is not a cosmetic gain. Carrying the published count doubles the
coefficient of the second term of the source's (5.17) from $0.89$ to $1.78$, and
the Type I right-hand side does not absorb that: in the worst admissible corner
the assembled bound then exceeds it by a factor $1.29$.

## The child

**`TaoFivePrimes.vinogradov_block_coprime`** is the single-block estimate: for
every integer $m$,

$$\sum_{m<n\le m+q}\mathrm{vmin}\Bigl(A,\frac B{|\sin(\pi\alpha'' n+\theta'')|}\Bigr)\ \le\ 2A+\frac2\pi Bq\log 4q,$$

under the hypotheses $\alpha''=\frac{a'}q+\beta$, $|\beta|\le q^{-2}$ and
$\gcd(|a'|,q)=1$. It is instantiated here with $\alpha''=2\alpha$ and
$\theta''=\pi\alpha+\theta$; the coprimality and approximation hypotheses are
exactly the statement's hypotheses on $2\alpha$, passed through unchanged.

## The reduction in Lean

The definition module `TaoFivePrimes_Theorem51VinogradovSharp` supplies the
three ingredients:

* `odd_sum_reindex` — the reindexing identity above, proved by `Finset.sum_bij`
  along $z\mapsto\frac{z-1}2$ (a bijection on odd integers, with no side
  condition because `Int.floor` is not clamped at zero);
* `blockBound_of_int_block` — the conversion from the platform's formulation of
  the block estimate, on `Finset.Ioc m (m+q)`, to a bound on the half-open real
  interval $(x',y']_{\mathbb Z}$ for $y'-x'\le q$; it uses nonnegativity of the
  summand to pass to the sub-range actually needed;
* `odd_block_from_block` — the assembly of the two, i.e. Corollary 3.5 from
  Lemma 3.4 at block count one.

The proof is therefore three lines: convert the child into `blockBound` on the
shifted endpoints $\bigl(\frac{x-1}2,\frac{y-1}2\bigr]$, apply
`odd_block_from_block` to get `oddBlockBound` on $(x,y]$, and discharge its width
hypothesis with the assumed $y\le x+2q$. The only arithmetic left over is the
conversion between `Real.log (4 * q)` (a natural-number product, as the child
states it) and `Real.log (4 * (q : ℝ))` (a real product, as the definition
module states it), which `norm_num` handles.

## Relation to the false formulations

The platform's `vinogradov_block_if_form` was **Disproved** and
`vinogradov_lemma_if_form` is false, both because they omit
$\gcd(|a'|,q)=1$: with $a'=0$ the phase is constant modulo $\pi$, every one of
the $q$ terms of a block contributes $A'$, and the right-hand side pays only
$2A'$. Both are recorded on their nodes. The present chain uses only the
corrected child, and the coprimality hypothesis is carried explicitly through
every level.
