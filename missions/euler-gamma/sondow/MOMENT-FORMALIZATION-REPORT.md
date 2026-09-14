# Logarithmic moments and finite boundary sums

This continuation completes the elementary logarithmic moment computation and its diagonal/off-diagonal finite sums. These are local, unconditional Lean proofs supporting the existing finite-cutoff route. No new platform node or submission was created in this continuation, and neither original analytic target is claimed complete.

## Completed mathematics

For real a,b >= 0, the double integral of x^a y^b / (-log(xy)) over the unit square equals 1/(a+1) when a=b, and log((b+1)/(a+1))/(b-a) otherwise. The proof establishes absolute integrability on the product of the Laplace-parameter half-line and the unit square before applying Fubini. It handles the boundary point 1 by an almost-everywhere argument. The reciprocal-log representation and the rational improper integral are proved explicitly from Mathlib's exponential integral and fundamental theorem of calculus.

Natural-exponent corollaries are included. Summation over a finite geometric cutoff is then evaluated: the diagonal becomes a difference of harmonic numbers, and each off-diagonal becomes a finite boundary sum of logarithms divided by the exponent difference. The proofs include the empty cutoff and are not numerical checks.

This formalizes the known route in [Sondow, Theorem 1](https://arxiv.org/pdf/math/0209070), equations (9)-(11). It is not a new irrationality argument.

## Files

- `Solutions/SondowRationalIntegral.lean`: rational improper integral (both cases), integrability, reciprocal logarithm as a Laplace integral, unit-interval power moment.
- `Solutions/SondowLogMoment.lean`: product-space absolute integrability, justified Fubini swap, double logarithmic moments for real and natural exponents.
- `Solutions/SondowFiniteSums.lean`: harmonic telescoping, discrete rectangle identity, logarithmic boundary telescoping.
- `Solutions/SondowFiniteMoments.lean`: combination of the integration and summation results.

## Verification

The command `lake build Solutions.SondowFiniteMoments` completed successfully, building the four modules. The workspace uses Lean v4.33.1, Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474, and `autoImplicit=false` in lakefile.lean. Every exported result has an explicit `#print axioms` check. All reports contain only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The final build emitted no warnings for these modules.

SHA256 of the validated files:

| File | SHA256 |
|---|---|
| SondowRationalIntegral.lean | 800861E50AF5D542CC25F35F048DFD4714FBEC86D3640F17DB8E4952B0A1E97E |
| SondowLogMoment.lean | 00955A8977E63C895336D55293451E98D1A1668AC5FB6B6A09C3AA5098BCF5E8 |
| SondowFiniteSums.lean | 7A2453EF4DD59B96F48D5B922515AB7D2CA591CD2B2EF34E3746931372D72AB0 |
| SondowFiniteMoments.lean | 1398A946DB38D11940E5084EBE9946B1C4B94C8C91415493575C64D73F2D6B7C |

## Remaining work

For the finite cutoff identity, expand the truncated kernel, justify finite-sum integration using the established moment integrability, pair the triangular sums, and connect the boundary log coefficients to the published positive-coefficient definition of L. The last connection requires Sondow's Lemma 2 / Appendix combinatorial identity. The completed limits and parent reduction remain reusable.

For the scaled bound, the previously reused Rosser--Schoenfeld branch remains the planned dependency. This continuation did not close its large-argument or finite-middle leaves. A weaker Chebyshev estimate cannot replace the exact quantitative requirement without an additional argument.

The fractional-part infinite-occurrence conjecture is still a mathematical open assumption. None of these formalization results proves it or the gamma irrationality milestone. The full two-target completion goal remains active.
