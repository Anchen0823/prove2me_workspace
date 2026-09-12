We reduce the quadratic sifted prime mass estimate to the explicit
two-sided Chebyshev bound

$$|\psi(y)-y|\le \frac{y}{40\log y}\qquad(y\ge10^8).$$

This is the sole unproved input. It is the estimate used in the proof of
Tao's Lemma 4.3, arXiv:1201.6656v4, citing Schoenfeld's Theorem 7.
All cutoff, summation, integration, and sieve-loss arguments below are
proved in the submitted reduction. No smoothness of the entire
trapezoid is assumed.

Write the unsifted and sifted quadratic masses as U and M. The target
hypotheses imply x at least 10^9 and log(x/10) at least 7.5. We prove

$$|U-\tfrac23 x|\le\frac{x}{20\log(x/10)},\qquad |M-U|\le\frac{x}{150}.$$

For the first bound, decompose the squared cutoff into the polynomials
(10t-1)^2, 1, and (9-10t)^2 on (1/10,1/5], (1/5,4/5], and (4/5,9/10],
respectively, and zero elsewhere. The proof checks all endpoints and
the corresponding floored finite summation intervals. Apply Abel
summation on each interval; the internal boundary terms cancel and
the outer boundary terms vanish.

The result is a difference of two integrals of psi against nonnegative
continuous kernels. Each kernel integrates to one. Replacing psi(t) by
t gives the main term (2/3)x by direct polynomial integration.
On the support, the source estimate and monotonicity of log give

$$|\psi(t)-t|\le\frac{x}{40\log(x/10)}.$$

Thus the two error integrals have total absolute value at most
x/(20 log(x/10)). Integrability follows from monotonicity of psi and
continuity of the polynomial kernels; continuity of psi is not assumed.

For the sieve loss, the cutoff vanishes at all natural numbers at most
sqrt(x). Every prime above that threshold is coprime to the inclusive
primorial used in the target. The weights lie between zero and one, so
the discarded mass is at most psi(x)-theta(x). Mathlib supplies

$$\psi(x)-\theta(x)\le2\sqrt{x}\log x.$$

An elementary logarithmic estimate, formalized here, bounds this by
x/150 for x at least 10^9. This avoids any further open prime-counting
estimate. Since log(x/10) is at least 7.5, the unsifted error is also
at most x/150. Hence

$$|M-\tfrac23 x|\le\frac{x}{75}.$$

Finally set epsilon equal to (M-(2/3)x)/((2/3)x). The denominator is
positive, the displayed bound gives absolute epsilon at most 0.02,
and the required mass identity follows by algebra.
