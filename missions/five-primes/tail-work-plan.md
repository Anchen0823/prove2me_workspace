# Complementary-correlation proof after the raw reduction

The generic multiplier estimate in `FiniteDifference.lean` is proved.
For an integer-indexed finitely supported complex sequence a, define its
Fourier transform as the finite sum of `a(n) e(n alpha)` and its difference
as `a(n) - a(n-1)`. The file represents the shift using `Finsupp.mapDomain`
and proves

$$|1-e(\alpha)|^2|\widehat a(\alpha)|
\le\sum_n|\Delta^2a(n)|.$$

Progress toward the published complementary-correlation child:

1. Represent the sampled cutoff as an integer-indexed finitely supported
   sequence; prove equality with the platform's finite polynomial, including
   both zero endpoints and all coefficients outside the natural range.
   **Completed** in `CutoffFourierDecay.lean`.
2. Use the exact hinge representation
   `eta1(t) = (10t-1)_+ - (10t-2)_+ - (10t-8)_+ + (10t-9)_+`.
   For each hinge, the second difference is nonnegative and its sum
   telescopes to `10/x`. This should give total second-difference mass at
   most `40/x` for the sampled cutoff. **Completed** in the expanded
   `CutoffDifferences.lean`; the finite-support norm bound is also proved.
3. Convert the multiplier to the chord lower bound and integrate over the
   two real tails. **Completed** in `CircleTail.lean` and
   `CircleTailIntegral.lean`, including endpoint handling.
4. Bound the prime-weighted polynomial by `psi(x) <= 6*x`.
   **Completed** in `PrimeUniformBound.lean` using Mathlib's elementary
   Chebyshev bound. No open Rosser-Schoenfeld theorem is needed.
5. Combine the bounds. **Completed** in `ComplementaryReduction.lean`.
   The proof uses only the size, upper-radius, and epsilon hypotheses;
   the target's mass identity is not needed.

The full exact-target solution passed local Lean verification with
`autoImplicit=false`. See `verification/correlation-proof-local-result.json`
for the source hash. Submission `bb88d850-1779-463a-9196-da6e7a951f88`
is ACCEPTED; the theorem is Proved. No open theorem is imported.

Useful current Mathlib APIs: `AddCircle.integral_haarAddCircle`,
`AddCircle.intervalIntegral_preimage`,
`AddCircle.norm_coe_eq_abs_iff`,
`intervalIntegral.integral_congr_Ioo_of_le`, and
`intervalIntegral.integral_mono_on_of_le_Ioo`. `integral_zpow` and
`intervalIntegrable_zpow` are in the root namespace, not in
`intervalIntegral`.
