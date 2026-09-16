This proves Corollary 3.5 **at the sharp block count**: on a range of odd
integers of width at most $2q$, the Vinogradov min-sum costs **one** block,

$$\sum_{\substack{x<n\le y\\ n\ \text{odd}}}\min\Bigl(A,\frac B{|\sin(\pi\alpha n+\theta)|}\Bigr)\ \le\ 2A+\frac2\pi Bq\log4q,$$

rather than the two blocks that the published covering count
$\lfloor(y-x)/(2q)\rfloor+1$ would give.

## Two remarks to make first

**The proof does not use `halpha`, `hbeta`, `hB`, or `a`.** That is deliberate and
not a gap. Step (b) below derives the numerical bound $qA\le 2A+\frac2\pi Bq\log4q$
from `hvino` alone, at the admissible instance $\alpha'=\beta'=\theta'=0$; every
summand is bounded by $A$ regardless of $\alpha$. So the statement in fact holds
**uniformly in $\alpha$ and $\theta$**. This is not a weakness — the sharp
count-1 form is "cheap" precisely because it pays $A$ per term instead of
exploiting cancellation across a block. It does mean the result carries less than
the full strength of the analytic input, and a downstream consumer that needs the
genuine $(2/\pi)Bq\log4q$ decay should still use `vinogradov_odd`.

`hA : 0 ≤ A` **is** used, when scaling the counting bound
`#S · A ≤ q · A` by `A ≥ 0`, so the nonnegativity hypothesis is not gratuitous.

## Why the obvious route fails

Reindex $n=2m+1$ and apply `hvino` to the reindexed range $(\frac{x-1}2,\frac{y-1}2]$.
Its width is $\frac{y-x}2$, which is exactly $q$ when $y-x=2q$ — precisely the case
at hand — and the covering count $\lfloor W/q\rfloor+1$ is then **2**, not 1. A
larger count is a *weaker* hypothesis, so the surplus block cannot be removed by
rewriting. This is arithmetic, not slack: $\lfloor q/q\rfloor+1=2$. (This is
exactly the obstruction that makes the count-1 form a separate statement from the
platform's already-Proved `TaoFivePrimes.vinogradov_odd`, whose conclusion keeps
the published count 2.)

## What the proof does instead

It never asks `hvino` to produce the count. Two independent steps.

**(a) Counting — the sum is at most $qA$.** Every summand is at most $A$: the
zero-of-sine branch returns $A$ outright, the other branch is $\min(A,\cdot)\le A$
(`blkSummand_le_A`). After the reindexing (`odd_sum_reindex`) the index set is the
half-open integer range $(\frac{x-1}2,\frac{y-1}2]$, whose width is $\frac{y-x}2\le q$.
Hence it sits inside a single width-$q$ integer interval
$\operatorname{Ioc}\lfloor\frac{x-1}2\rfloor(\lfloor\frac{x-1}2\rfloor+q)$, which has
**exactly** $q$ elements by `Int.card_Ioc` (`card_Ioc_width_q`). With
$\sum \le \#S\cdot A$ (`sum_le_card_nsmul`) and $\#S\le q$, the sum is at most $qA$.

Note what is *not* needed here: no integer division by 2, no floor-of-half
bookkeeping on the count. The count comes from a width-$q$ interval cardinality,
which is why this part is robust.

**(b) A degenerate instance — $qA$ is at most the right-hand side.** Instantiate
`hvino` at $\alpha'=\beta'=\theta'=0$, $u=-\tfrac12$, $v=q-\tfrac34$. Then:

* every summand is exactly $A$ — the sine vanishes identically, so the *first*
  branch of the `if` fires (`degenerate_summand`);
* there are exactly $q$ terms, namely the integers $-1<n\le q-1$
  ($\lfloor-\tfrac12\rfloor=-1$, $\lfloor q-\tfrac34\rfloor=q-1$);
* the covering count is $1$, because $v-u=q-\tfrac14<q$ gives
  $\lfloor(q-\tfrac14)/q\rfloor+1=1$.

So the instance *is* the inequality $qA\le 2A+\frac2\pi Bq\log4q$. This is the one
place `hvino` is used.

Chaining (a) and (b) proves the claim.

## Sign conventions and the zero-of-sine trap

The summand is defined with the source's convention: it returns $A$ where the sine
vanishes. A bare `min A (B / |sin ...|)` would silently contribute
$\min(A,B/0)=\min(A,0)=0$ at a vanishing phase, because Lean's real division
returns $0$ there — which would make step (b) give $0$ instead of $qA$ and the
degenerate instance vacuous. The `if`-form is therefore load-bearing, not cosmetic.

## Source

Tao, *Every odd number greater than 1 is the sum of at most five primes*,
arXiv:1201.6656, Section 3 for Lemma 3.4 / Corollary 3.5 and Section 5.2 for the
blocks $2jq+\tfrac q2<d\le 2(j+1)q+\tfrac q2$ of width exactly $2q$ on which the
count-1 form is used. The analytic content of Lemma 3.4 is carried by `hvino` and
is not re-proved here.

## Note to reviewers on scope

This node currently sits **outside** the five-primes mission DAG (published
standalone; its dependency graph has no edges). Its natural place is as a child
of the Type I block-summation chain, alongside `TaoFivePrimes.vinogradov_odd`.
