This is a reduction of the raw major-arc bound to two analytic inputs.
Under the target's stated hypotheses it proves

$$\exists\varepsilon,\quad |\varepsilon|\le0.02,\qquad
0.999[0.99(1+\varepsilon)]^2x\le\frac32
\int_{\operatorname{majorArc}(x)}|S_1(x,\alpha)|^2\,d\alpha.$$

The argument follows the correlation method in Tao, arXiv:1201.6656v4,
Proposition 4.8 (printed pp. 19–20) and Corollary 4.9 (printed p. 20),
specialized to the Section 8 trapezoid. The normalization factor 3/2
is retained. The submitted reduction has two unproved dependencies:
`TaoFivePrimes.eta1_quadratic_prime_mass` and
`TaoFivePrimes.eta1_complementary_correlation`.

Write F for the finite Fourier polynomial with coefficients eta1(n/x),
M for the quadratic sifted prime mass, E for the major arc, and A for
the integral of |S1| squared over E. Orthogonality of integer characters
gives the exact identities

$$\int S_1\overline F=M,\qquad
\int |F|^2=\sum_{n=0}^{x}\eta_1(n/x)^2.$$

These identities are proved in the reduction, using Mathlib's
orthonormal Fourier characters and finite-sum integration.

The literal platform cutoff is handled directly. Its five polynomial
pieces give

$$0\le\eta_1\le1,\qquad \int_0^1\eta_1(t)^2\,dt=\frac23.$$

The distance-to-an-interval definition yields a Lipschitz constant 10
for eta1 and the one-sided bound

$$\eta_1(u)^2\le\eta_1(v)^2+20|u-v|.$$

Integrating this on each scaled unit cell and observing that eta1(1)=0
proves, for every positive integer x,

$$\sum_{n=0}^{x}\eta_1(n/x)^2\le\frac23x+20=:D.$$

This bound is proved here, not imported as an open child. It has more
slack than the smooth variation estimate in the source but needs no
smooth approximation and is sufficient under the target's size bound.

The first child supplies a real epsilon with

$$|\varepsilon|\le0.02,\qquad M=\frac23(1+\varepsilon)x.$$

The second child, with that mass identity as a hypothesis, supplies

$$\left|\int_{E^c}S_1\overline F\right|\le0.01M.$$

These two estimates are assumptions of the reduction. The explicit
prime estimate, prime-power removal, Fourier-tail estimate, and their
justification for the nonsmooth cutoff are not claimed as proved here.

Splitting the global correlation into E and its complement, using the
triangle inequality, and applying Cauchy–Schwarz on the restricted Haar
measure gives

$$ (0.99M)^2\le A\int_E|F|^2\le AD.$$

Finally the target's condition x/10 at least 10^8 implies x at least
10^9, hence x at least 30000. Therefore

$$0.999D\le\frac23x.$$

Combining the last two inequalities with the exact formula for M gives
the stated raw lower bound, with precisely the original constants and
without adding a hypothesis to the target.
