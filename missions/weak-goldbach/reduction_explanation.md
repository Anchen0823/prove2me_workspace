We prove that every even natural number strictly above Richstein's verified range up to $4\cdot10^{14}$ and at most $4\cdot10^{18}$ is a sum of two primes:

$$
\forall m\in\mathbb N,\qquad 4\cdot10^{14}<m,\quad m\le 4\cdot10^{18},\quad 2\mid m
\ \Longrightarrow\ \exists\,p,q\in\mathbb N,\ \ p\ \text{prime},\ q\ \text{prime},\ m=p+q .
$$

These are exactly the three hypotheses of the target: a strict lower bound, the upper bound, and evenness. The two summands are ordered as $p+q$ on the right, matching the target's conclusion.

## Proof idea

The statement is a computational verification claim, and the reduction isolates its entire computational content in a single child lemma, `WeakGoldbach.verified_range_sieve_coverage`, which is expressed in the finite sieve-coverage language that this platform already uses for Richstein's range. What remains to be argued here is elementary: an integer in the range which has no prime divisor at most $2\cdot10^{9}$ other than itself must be prime, because otherwise its least prime factor would be at most its square root, and every integer in the range is at most $(2\cdot10^{9})^{2}=4\cdot10^{18}$. Thus the child lemma's set inclusion converts directly into a Goldbach partition.

## Step 1 — Localisation in a block of one million

Write

$$
B=4\cdot10^{14},\qquad W=10^{6},\qquad N=4\cdot10^{18},
$$

and for $m$ in the target range put

$$
b=\left\lfloor\frac{m-B}{W}\right\rfloor .
$$

Since $m>B$ by hypothesis, $m-B$ is the honest integer difference. The division algorithm gives $m-B=bW+r$ with $0\le r<W$, hence

$$
B+bW\ \le\ m\ \le\ \min\bigl(N,\ B+(b+1)W-1\bigr),
$$

the second bound combining $m\le N$ (a hypothesis) with $m<B+(b+1)W$. Moreover

$$
b\ \le\ \frac{N-B}{W}=3\,999\,600\,000\,000\ <\ 4\cdot10^{12}+1,
$$

so the block index lies in the range covered by the child lemma. Consequently $m$ is an element of the finite set

$$
\Bigl\{\,n\in\bigl[\max(4,\,B+bW),\ \min\bigl(N,\,B+(b+1)W-1\bigr)\bigr]\ :\ 2\mid n\,\Bigr\},
$$

which is the hypothesis required by the child lemma at this index $b$ (evenness being the target's third hypothesis).

## Step 2 — The child lemma

`WeakGoldbach.verified_range_sieve_coverage` asserts that for every $b<4\cdot10^{12}+1$,

$$
\Bigl\{\,n\in[L_b,U_b]:2\mid n\,\Bigr\}\ \subseteq\
\bigcup_{\substack{p\le 9781\\ p\ \text{prime}}}\bigl(p+S(L_b-9781,\ U_b,\ 2\cdot10^{9})\bigr),
$$

where $L_b=B+bW$, $U_b=\min(N,B+(b+1)W-1)$, and $S(lo,hi,R)$ denotes the set of $q\in[\max(2,lo),hi]$ having no prime divisor $r\le R$ other than $q$ itself. The bound $9781$ is the largest smaller prime occurring in a minimal Goldbach partition of an even number at most $4\cdot10^{18}$, attained at $n=3\,325\,581\,707\,333\,960\,528$, and $2\cdot10^{9}$ is the square root of the range endpoint. The uniformity across the $4\cdot10^{12}+1$ blocks is what makes this a single obligation rather than a family of unrelated ones.

This lemma is an assumption of the present submission, not a result of it. It is the irreducible computational core — the segment of Oliveira e Silva–Herzog–Pardi above Richstein's limit — stated in the certificate form so that it can be attacked, or computed, on its own.

## Step 3 — Coverage produces a representation

Applying Step 2 to $m$ gives a prime $p\le9781$ and an element $q\in S(L_b-9781,\ U_b,\ 2\cdot10^{9})$ with $p+q=m$. So it remains only to know that $q$ is prime.

## Step 4 — Survivors of a complete sieve are prime

This is the sieve-soundness step, proved inside the submission as `GoldbachSieve.survivor_prime`. Let $q\in S(lo,hi,R)$ with $hi\le R^{2}$. By definition $q\ge\max(2,lo)\ge2$, so $q\ne1$. Suppose $q$ is not prime. Let $r$ be its least prime factor. Then $r$ is prime, $r\mid q$, and $r\ne q$ because $q$ is not prime while $r$ is. Also

$$
r^{2}\ \le\ q\ \le\ hi\ \le\ R^{2},
$$

using the defining inequality $r^{2}\le q$ for a least prime factor of a composite number, so $r\le R$. Therefore $r$ is a prime at most $R$ dividing $q$ and distinct from $q$ — precisely a witness that $q$ does not belong to $S(lo,hi,R)$, a contradiction. Hence $q$ is prime.

The companion lemma `GoldbachSieve.pairSums_sound` assembles Steps 3 and 4: if $hi\le R^{2}$ and $n$ lies in the union of the translates, then $n$ is a sum of two primes.

## Step 5 — The bound applies and the target follows

Here $hi=U_b\le N=(2\cdot10^{9})^{2}$, so Step 4 applies with $R=2\cdot10^{9}$ and the survivor $q$ is prime. Step 3 then exhibits $p$ and $q$ prime with $m=p+q$, which is the target statement, with the summand order read off from the child lemma.

## What the reduction buys

The parent quantifies over all $2\cdot10^{18}$ even values in an interval of length $4\cdot10^{18}$ and asserts an existential statement about each of them. The child replaces that with one uniform finite-set inclusion, indexed by a block counter, over the same data, and the reduction supplies the arithmetic that connects the two: the block partition, its index range, and the square-root completeness of the sieve cutoff. The parameters that are genuinely specific to the extension segment — the small-prime bound $9781$ and the cutoff $2\cdot10^{9}$ — appear only in the child, and they differ from the ones for Richstein's range, so the child is not a restatement of any existing node.
