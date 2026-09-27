# Proof: injectivity of the family parametrisation

The map $n\mapsto(1,\;n^2-n+1,\;2n-1,\;n^2-n-1)$ is injective on all of `ℤ`.

**Argument.** The third coordinate is the affine function $2n-1$, and an affine function with
nonzero slope recovers its argument. Concretely, from an equality of quadruples, applying the
coordinate projection $t\mapsto t_{2,2,1}$ yields $2m-1=2n-1$, and `omega` turns that into
$m=n$ by linear integer arithmetic.

**Why no monotonicity hypothesis.** The recovery goes through the *linear* coordinate, not the
quadratic one $n^2-n+1$, so the argument does not need $n\ge1$ or any monotonicity of the
quadratic — hence no restriction on $n$ appears in the statement. (The quadratic coordinate
is genuinely two-to-one on `ℤ`, since $n^2-n+1$ is symmetric about $n=\tfrac12$; using it
would have forced a hypothesis.)

**Implementation notes.** The quadruple is a right-nested product, so the third coordinate is
`t.2.2.1` of type `ℤ × ℤ × ℤ × ℤ`. `congrArg` with that projection and `simpa` extract the
coordinate equality; `omega` closes the linear step.
