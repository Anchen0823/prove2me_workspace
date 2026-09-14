We prove the exact finite-cutoff identity directly, without importing open theorems.

Expand the truncated geometric factor and both binomial factors. Absolute integrability justifies every exchange of integration and finite summation. The elementary logarithmic moments are evaluated by inserting the Laplace representation of the reciprocal logarithm and applying Fubini; the resulting rational improper integral is computed by the fundamental theorem of calculus. Diagonal moments telescope to harmonic differences, and off-diagonal moments telescope to short logarithmic boundary sums.

The signed logarithmic form is identified with the published positive form L, rather than changing its definition. Pascal recurrence proves the finite row identity

$$\sum_{j=0}^n\frac{(-1)^j\binom nj}{j-k}=(-1)^k\binom nk(H_k-H_{n-k}),$$

where the diagonal summand is zero. Antisymmetry then gives the rectangle identity in Sondow's Appendix; reflection truncates its harmonic prefix at the required minimum. A bijection of the finite triple-index domains identifies the coefficients of every logarithm.

Finally, the alternating binomial sum and Vandermonde identity give the coefficient of H_N-log(N); all remaining shifts agree exactly with cutoffError. This formalizes Theorem 1, equations (9)-(11), and Lemma 2 of [Sondow v2](https://arxiv.org/pdf/math/0209070). The submitted file is self-contained apart from Mathlib and the published definitions; its local axiom check has no sorryAx.
