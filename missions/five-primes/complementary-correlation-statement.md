Let x be a positive integer, let eta1 be Tao's Section 8 trapezoidal cutoff,
and put

$$r=\frac{T_0}{3.6\pi x},\quad T_0=3.29\cdot10^9,\quad
F_x(\alpha)=\sum_{n=0}^{x}\eta_1(n/x)e(n\alpha).$$

The unit circle carries probability Haar measure, and E is the closed arc
defined by distance at most r from zero. Let S1 be the sifted prime-weighted
Fourier polynomial from the arc-split definition. Assume

$$\frac1{2x}\le r\le\frac12,\quad 10^8\le x/10,\quad 10^4(3/2)\le x,$$
$$5(3/2)\le\log(x/10),\quad10^8(9/4)\le x,\quad
20\cdot60\sqrt{3/2}\le\frac{T_0}{3.6\pi}.$$

Suppose a real epsilon satisfies

$$|\varepsilon|\le0.02,\qquad
M_x:=\sum_{n=0}^{x}\Lambda(n)\mathbf1_{(n,\sqrt{x}\#)=1}\eta_1(n/x)^2
=\frac23(1+\varepsilon)x.$$

Then the complementary correlation obeys

$$\left|\int_{E^c}S_1(x,\alpha)\overline{F_x(\alpha)}\,d\alpha\right|
\le0.01M_x.$$

This isolates the tail step in the proof of Proposition 4.8 and its
one-percent comparison in Corollary 4.9, after specializing to Section 8.
The mass approximation is an explicit hypothesis, not a conclusion of
this lemma. A proof must supply the exponential-sum tail estimate and
the required linear prime-mass control for the literal nonsmooth cutoff,
by a justified approximation or a direct variation argument. Unlike the
parent theorem, this controls a complementary mixed integral rather than
the major-arc square integral.
