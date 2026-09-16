This is the outstanding computational obligation in a sieve-based formalization of the Oliveira e Silva–Herzog–Pardi extension of Richstein's verified binary Goldbach range.

Put

$$
B = 4\cdot 10^{14},\qquad N = 4\cdot 10^{18},\qquad W = 10^{6}.
$$

For an integer $0\le b\le 4\cdot 10^{12}$ let

$$
L_b = B + bW,\qquad U_b = \min\bigl(N,\ B + (b+1)W - 1\bigr),
$$

so that the intervals $[L_b,U_b]$ tile $[B,N]$, the last one being the single point $N$ itself. Let

$$
S(lo,hi,R) = \{\,q \in [\max(2,lo),\,hi]\ :\ \text{no prime } r\le R \text{ divides } q \text{ other than } q \text{ itself}\,\}
$$

be the set of survivors of sieving the interval $[\max(2,lo),hi]$ by the primes up to the cutoff $R$, and let

$$
C(P,lo,hi,R) \;=\; \bigcup_{\substack{p\le P\\ p\ \text{prime}}}\ \bigl(p + S(lo,hi,R)\bigr)
$$

be the union of the translates of $S$ by all primes up to the small-prime bound $P$. Both are the finite sets introduced in `GoldbachSieve`.

The assertion is that for every $0\le b\le 4\cdot 10^{12}$,

$$
\{\,n\in[L_b,U_b]\ :\ 2\mid n\,\}\ \subseteq\
C\bigl(9781,\ L_b - 9781,\ U_b,\ 2\cdot 10^{9}\bigr).
$$

In words: each even number in each block of one million above Richstein's range is the sum of a prime $p\le 9781$ and an integer $q\le U_b$ that has no prime divisor $\le 2\cdot10^{9}$ other than itself. Since $U_b\le N=(2\cdot 10^{9})^{2}$, such a $q$ is prime, so the inclusion says exactly that every even $n$ in $[L_b,U_b]$ has a Goldbach partition whose smaller prime is at most $9781$.

This statement is the segment of the verified binary Goldbach range strictly above Richstein's $4\cdot10^{14}$, expressed in the certificate language already used for the Richstein range, and it is the only computational input needed for `WeakGoldbach.verified_two_primes_4e14_to_4e18`. The numerals are the ones reported for the computation: $9781$ is the largest smaller prime occurring in a minimal Goldbach partition of an even number $\le 4\cdot10^{18}$, attained at $n = 3{,}325{,}581{,}707{,}333{,}960{,}528$. The sieve cutoff $2\cdot10^{9}$ is forced by the square-root completeness argument at height $4\cdot10^{18}$, and therefore differs from the cutoff $2\cdot10^{7}$ used for Richstein's range.

**Formalization Note** The block width $10^{6}$, the block index range $b<4\cdot10^{12}+1$, the small-prime bound $9781$ and the sieve cutoff $2\cdot10^{9}$ are this formalization's choices, mirroring `Richstein2001.segmented_sieve_coverage`; they describe the certificate interface, not the original program. Survivors are defined by a cardinality-zero condition, so both sets are executable finite filters and unions. The first block includes the endpoint $B=4\cdot10^{14}$ and the last block includes the endpoint $N$; no certificate data or Lean verification of the blocks is supplied with this statement.
