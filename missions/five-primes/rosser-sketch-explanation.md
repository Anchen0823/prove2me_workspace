We reduce the uniform Rosser--Schoenfeld inequality

$$\sum_{m\le n}\Lambda(m)<1.03883n\qquad(n\ge1)$$

to two explicit remaining inputs: the finite inequality for integers strictly
between 1000 and $10^8$, and the two-sided Chebyshev estimate

$$|\psi(y)-y|\le\frac{y}{40\log y}\qquad(y\ge10^8).$$

Both inputs are assumptions of this sketch. The small range through 1000 is
proved within the submitted file by exact arithmetic, without an open input.

For the small range, use Mathlib's identity

$$\psi(n)=\log\operatorname{lcm}(1,\ldots,n).$$

Exact integer certificates bound successive least common multiples by powers
of two. The rigorous bound $\log2\le0.693147181$ converts these certificates
to upper bounds for $\psi$. The bounds at upper endpoints cover 87 intervals
because $\psi$ is nondecreasing, while the desired upper bound increases with
the argument. The interval coverage and integer comparisons are checked in
Lean. At 31 and 32, taking a small integer power retains enough fractional
precision. At 113, an exact least common multiple and a rational mantissa
bound are combined with logarithm series estimates with proven remainders.
This yields a complete proof for every integer from 1 through 1000.

For the large range, the imported two-sided estimate gives

$$\psi(y)\le y+\frac{y}{40\log y}.$$

Here $\log y\ge1$, so

$$\psi(y)\le1.025y<1.03883y.$$

The only range not covered by these two arguments is

$$1000<n<10^8.$$

That finite certificate is the other open child of the reduction. Numerical
scouting is not used as a proof of this child. Finally, the sum in the target
is identified with Mathlib's Chebyshev function; its additional term at zero
vanishes. The three ranges therefore exhaust the exact target's domain.
