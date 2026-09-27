# Proof: infinitely many distinct patterns

The range of the parametrisation $n\mapsto(1,\;n^2-n+1,\;2n-1,\;n^2-n-1)$ is an infinite subset
of `ℤ × ℤ × ℤ × ℤ`.

**Argument.** An injective function from an infinite type has infinite range, so the statement
is a direct application of `Set.infinite_range_of_injective` to the injectivity proof: from an
equality of quadruples, the third coordinate gives $2m-1=2n-1$, and `omega` concludes $m=n$.

**Interpretation.** Together with the companion statement that each member is a positive
solution with four pairwise distinct entries (for $n\ge4$), this says the equation
$a^2+b^2=c^2+d^2$ has infinitely many genuinely different nontrivial solutions, one for each
$n\ge4$. It is an existence statement about the family only; it does not assert that every
solution lies in the family, which is the mission's goal and is not used here.

**Implementation notes.** No hypothesis on $n$ is needed because the injectivity argument uses
the linear coordinate. The infinitude is over the whole parameter range, not merely over
$n\ge4$; restricting to $n\ge4$ would also be infinite but would require extra work to express.
