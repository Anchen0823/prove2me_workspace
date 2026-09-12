This reduction establishes the complementary Fourier correlation bound

$$\left|\int_{E^c}S_1(x,\alpha)\overline{F_x(\alpha)}\,d\alpha\right|
\le0.01\left(\frac23(1+\varepsilon)x\right)$$

under the target's exact hypotheses. Here E is the closed major arc of
radius r, and F is the finite Fourier polynomial whose coefficients are
the Section 8 trapezoid sampled at n/x. The only unproved dependency is
`TaoFivePrimes.rosser_schoenfeld_psi_bound`, an existing source theorem
asserting the explicit von Mangoldt upper bound. The discrete Fourier
and integration arguments below are proved in this reduction.

The argument implements the tail step of Tao, arXiv:1201.6656v4,
Proposition 4.8 (printed pp. 19–20) directly for the nonsmooth Section 8
cutoff. Its hinge decomposition is

$$\eta_1(t)=(10t-1)_+-(10t-2)_+-(10t-8)_++(10t-9)_+.$$

Each hinge has nonnegative second differences. Their finite sums
telescope, and each contributes exactly 10/x once x is at least 10.
The triangle inequality therefore gives total absolute second difference
at most 40/x for the cutoff. The implementation uses an integer-indexed
finitely supported sequence and proves its support and zero-extension
properties, including the boundary terms at the ends of the natural
summation range.

Shifting this sequence multiplies its Fourier transform by e(alpha).
Applying the shift identity twice and bounding a finite sum by the sum
of norms gives

$$|1-e(\alpha)|^2|F_x(\alpha)|\le\frac{40}{x}.$$

On the centered fundamental interval, Jordan's sine inequality gives

$$|1-e(t)|=2|\sin(\pi t)|\ge4|t|\qquad(|t|\le1/2).$$

Consequently, away from zero,

$$|F_x(t)|\le\frac{5}{2xt^2}.$$

The probability Haar integral on the unit circle is identified with the
integral on the centered real interval. The complement indicator vanishes
on the central interval. The two outer intervals are compared with the
inverse-square function; integral congruence on open intervals handles
the closed major-arc endpoints without asserting false pointwise
equalities there. This proves

$$\int_{E^c}|F_x(\alpha)|\,d\alpha\le\frac5{xr}.$$

The target fixes its radius by

$$xr=\frac{T_0}{3.6\pi},\qquad T_0=3.29\cdot10^9.$$

Using pi less than 4, this product is at least 5000, so the preceding
integral is at most 1/1000. No smooth approximation is assumed.

The cutoff lies between zero and one, the sifted von Mangoldt weights
are nonnegative and bounded by the ordinary weights, and each character
has modulus one. Thus

$$|S_1(x,\alpha)|\le\sum_{n=0}^{x}\Lambda(n).$$

The existing open Rosser–Schoenfeld source supplies

$$\sum_{n=0}^{x}\Lambda(n)<1.03883x.$$

It follows that the correlation norm is at most 1.03883x/1000. Finally,
the target's error hypothesis implies epsilon is at least -0.02, and

$$\frac{1.03883}{1000}x
\le0.01\cdot\frac23(1+\varepsilon)x.$$

The mass identity in the target is compatible with this conclusion but
is not needed for this stronger absolute estimate. The explicit prime
upper bound remains an assumption of this sketch; it is not claimed as
proved by the Fourier argument.
