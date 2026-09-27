# Proof: the explicit one-parameter family

The claim is that for every integer $n$,
$$1^2+(n^2-n+1)^2=(2n-1)^2+(n^2-n-1)^2 .$$

**Argument.** It is a polynomial identity in $n$, so `ring` closes it in one line. Expanding,
the left side is $1+(n^2-n)^2+2(n^2-n)+1 = n^4-2n^3+3n^2-2n+2$ and the right side is
$(4n^2-4n+1)+(n^4-2n^3-n^2+2n+1) = n^4-2n^3+3n^2-2n+2$; they agree.

**Why this family.** It is the cheapest source of solutions whose four entries are pairwise
distinct: the smallest entry is the constant $1$, which also makes every member primitive
and rules out one member being a nontrivial integer multiple of another. The equality part
needs no hypothesis at all — it holds for every integer $n$, including negative ones — and
only the positivity/distinctness part requires $n\ge4$.

**Sharpness of the bound.** At $n=3$ the two entries $2n-1=5$ and $n^2-n-1=5$ coincide, so
the threshold $n\ge4$ used in the companion statements cannot be lowered.
