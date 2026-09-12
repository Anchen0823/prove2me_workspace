# A finite-polynomial route to the raw major-arc bound

This is an implementation plan with an explicit dependency boundary, not a
completed proof of the analytic number-theoretic inputs.

Source: T. Tao, *Every odd number greater than 1 is the sum of at most five
primes*, arXiv:1201.6656v4, Proposition 4.8 (printed pp. 19–20),
Corollary 4.9 (printed p. 20), and the Section 8 trapezoidal cutoff.

Write `w(n) = siftedVonMangoldt x n`, `eta(n) = eta1(n/x)`, and define

\[
 F_x(\alpha)=\sum_{n=0}^x\eta(n)e(n\alpha),\quad
 M_x=\sum_{n=0}^x w(n)\eta(n)^2,\quad
 A_x=\int_{\mathrm{majorArc}(x)}|S_1(x,\alpha)|^2.
\]

The exact Fourier correlation is
\[
 \int S_1\overline{F_x}=M_x.
\]
This follows from orthogonality of the integer characters. The same argument
gives the exact Parseval identity `integral |F_x|^2 = sum eta(n)^2`.
Both identities use precisely the finite summation range in the platform
definition; no infinite series or prime asymptotic is involved.

For any measurable arc E, write the correlation as its integral over E plus
its integral over the complement. If the complementary integral has norm at
most delta, where `0 <= delta <= M`, Cauchy–Schwarz on E gives

\[
 (M-\delta)^2\le
 \left(\int_E|S_1|^2\right)\left(\int_E|F_x|^2\right)
 \le A_x D
\]

whenever the global test-function energy is at most `D > 0`.

## Specialized estimates and implementation status

1. **Quadratic prime mass:** there exists `eps` with `|eps| <= 0.02` and
   `M_x = (2/3)(1+eps)x`. This is the normalized specialization of (4.13),
   with the prime-power removal and explicit prime-mass estimate retained.
2. **Test-function energy (proved with sufficient slack):**
   `sum eta1(n/x)^2 <= (2/3)x + 20` for every positive integer x.
   `CutoffEnergy.lean` directly proves the five-piece formula for the literal
   platform cutoff and its squared integral `2/3`. It then proves the
   pointwise estimate `eta1(u)^2 <= eta1(v)^2 + 20 |u-v|` and integrates it
   on each unit cell after scaling by x. The endpoint at n=x is zero.
   This avoids a smoothness assumption or an approximation limit. The bound
   has a larger error than the source's variation estimate, but preserves
   the exact target under its existing size hypotheses.
3. **Complementary correlation:** the norm of
   `integral over majorArc(x)^c of S1 * conj F_x` is at most `0.01 M_x`.
   Following Proposition 4.8, first bound it by the nonnegative linear prime
   mass times `integral over the complement of |F_x|`, and then bound the
   latter using discrete second differences or a justified variation argument.
   The tail inequality is not established by Parseval alone.

With these inputs, take `delta = 0.01 M_x` and `D = (2/3)x + 20`. The target's
`hc8` implies `10^9 <= x`, hence `30000 <= x`, which implies

\[
 0.999\bigl((2/3)x+20\bigr)\le(2/3)x.
\]

Consequently the local correlation inequality implies exactly

\[
 0.999[0.99(1+\varepsilon)]^2 x\le\tfrac32 A_x.
\]

The factor `3/2` is preserved throughout. These estimates concern
distinct mathematical objects; none is an equivalent restatement of the
target's major-arc energy lower bound. They have not yet been published as
new platform children. Existing platform lemmas must be checked for reuse
before any publication.

## Local implementation

- `examples/five-primes/FourierMoments.lean`: character orthogonality, finite
  Fourier correlation, Parseval, and the exact `S1` quadratic-mass identity.
- `examples/five-primes/LocalL2.lean`: continuous-function Cauchy–Schwarz,
  localization with a complementary correlation error, and the final
  normalization arithmetic.
- `examples/five-primes/CutoffEnergy.lean`: piecewise cutoff formulas, exact
  squared integral, one-sided Lipschitz estimates, and the discrete bound.
- `examples/five-primes/MajorArcReduction.lean`: specialization of the checked
  helpers, with prime mass and complementary correlation as explicit
  hypotheses. Consult the validation record for its current compile status.

No imported open theorem is used in these files. Compilation results
are recorded separately in `verification/`; successful local helper checks
do not establish the two remaining specialized analytic estimates.
