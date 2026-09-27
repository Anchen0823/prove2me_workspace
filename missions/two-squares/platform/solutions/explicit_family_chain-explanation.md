# Proof: positivity and distinctness as a strict chain

For $n\ge4$ the four entries of the family are strictly ordered:
$$1\;<\;2n-1\;<\;n^2-n-1\;<\;n^2-n+1 .$$

**Argument.** Three separate integer inequalities, each discharged by `nlinarith` from the
single hypothesis $4\le n$:

* $1<2n-1$ is linear;
* $2n-1<n^2-n-1$ is $n^2-3n=n(n-3)>0$, and `nlinarith` derives it unaided from $4\le n$ — it
  multiplies hypotheses itself, so no hand-written `mul_pos` scaffolding is needed;
* $n^2-n-1<n^2-n+1$ is the trivial $-1<1$.

**Why a chain rather than six disequalities.** The chain fixes the size order of the four
entries, which is what later arguments actually consume: positivity follows from the first
inequality and $0<1$, distinctness follows from transitive `lt_trans` plus `ne_of_lt`, and
the ordering itself is what makes primitivity and the non-scaling statement immediate. A bare
list of disequalities, or a `Finset.card = 4` statement, would throw that information away.

**Sharpness.** At $n=3$ we get $2n-1=5=n^2-n-1$, so $4$ is the smallest admissible threshold.
