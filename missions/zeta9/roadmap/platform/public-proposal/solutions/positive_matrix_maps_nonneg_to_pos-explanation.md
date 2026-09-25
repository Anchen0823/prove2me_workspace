# Proof: an entrywise positive matrix maps the nonnegative cone into the positive cone

The submission proves that for a real $5\times5$ matrix $M$ with all entries strictly
positive and a nonzero vector $v\ge0$ entrywise, every coordinate of $Mv$ is strictly
positive.

**Argument.** By `Matrix.mulVec_apply`, the $i$-th coordinate is $\sum_jM_{ij}v_j$.
Each summand is nonnegative because $M_{ij}>0$ and $v_j\ge0$. Because $v\ne0$ and $v$
is entrywise nonnegative, some index $j_0$ has $v_{j_0}>0$; then $M_{ij_0}v_{j_0}>0$
for every row $i$, since every entry of $M$ is strictly positive. A finite sum of
nonnegative terms with at least one strictly positive term is strictly positive
(`Finset.sum_pos'`), and this holds for each coordinate.

**Notes on the hypotheses.** All fifteen positivity hypotheses are used: the strict
positivity of the entries is what upgrades "nonnegative sum" to "positive sum", and
without it the conclusion is false. Non-vanishing of $v$ is used to produce a strictly
positive coordinate; the entrywise-nonnegative hypothesis supplies the rest. The
argument also gives that a positive matrix raises the cone in one step, which is the
shape needed when the transfer matrix is strictly positive; when only the two-step
matrix $H_nH_{n+2}$ is positive, the same lemma applied to that product gives the
corresponding two-step statement.

**Scope.** This is one step of local node TA, isolated because the note's one-step
transfer has mixed signs and therefore fails to preserve the cone while the two-step
transfer does not. It does not formalise the limit matrix, the eventual positivity of
the actual two-step transfer, the Perron lower bound, the $-10.1109$ width rate, or the
identification of the eventual coefficient sign with the sign of the real value.
