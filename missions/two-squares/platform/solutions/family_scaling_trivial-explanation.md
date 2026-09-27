# Proof: no member of the family is a scalar multiple of another

If $(1,\,n^2-n+1,\,2n-1,\,n^2-n-1)=k\cdot(1,\,m^2-m+1,\,2m-1,\,m^2-m-1)$ for integers
$m,n,k$, then $n=m$.

**Argument.** Compare first coordinates. Scalar multiplication on a product acts coordinatewise,
and the first coordinate of the left-hand side is $1$ while that of the right-hand side is
$k\cdot 1=k$; hence $k=1$. The hypothesis therefore degenerates into an equality of two
quadruples, and injectivity of the parametrisation (proved by comparing the linear coordinate
$2n-1$) gives $n=m$.

**Why this captures "inequivalent patterns".** The mission regards scalar multiples as the same
basic pattern. Since every member of the family carries the entry $1$, the only scalar that can
carry one member to another is $1$ itself — so distinct parameters give patterns that are not
only unequal but not even multiples of one another. No positivity hypothesis on $k$ is needed:
negative and zero scalars are excluded automatically by the first-coordinate comparison.

**Implementation notes.** `congrArg` with the first projection followed by `simpa` proves
$k=1`; rewriting with it turns the hypothesis into a plain equality, and `simp` reduces
$1\bullet x$ to $x$ using `one_smul`.
