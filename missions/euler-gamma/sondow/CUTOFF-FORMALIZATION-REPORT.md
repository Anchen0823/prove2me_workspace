# Finite cutoff formalization

The analytic evaluation of the finite cutoff is now complete locally. The proof proceeds from the original integral and remainder definitions to a finite harmonic/logarithmic expression, then extracts the binomial coefficient of H_N-log(N) and the exact published cutoffError. No analytic evaluation hypothesis or open platform theorem is imported.

## Exact boundary

`finite_cutoff_signed_identity` proves the original finite-cutoff formula with `signedLogForm n` in place of `L n`. The signed form is the negative twice-triangular sum of the alternating binomial coefficients divided by j-i, times the short sum of log(n+i+k+1). It is Sondow's signed logarithmic expression, with the triangle and index shifts written explicitly.

`finite_cutoff_identity_of_logarithmic_forms_equal` has the exact original finite-cutoff conclusion and only one additional hypothesis: `signedLogForm n = L n`. This is a transparent conditional theorem, not an unconditional solution of the platform target. The published definition of L is unchanged.

## Completed proof chain

1. `SondowKernelExpansion.lean`: finite binomial numerator expansion and geometric truncation, with the geometric pole excluded explicitly.
2. `SondowTruncatedIntegral.lean`: integrability on the square, including the original kernel and cutoff kernel; identification of iterated and product integrals; exchange of all finite sums with integration. The dominating reciprocal-log kernel is supplied by the already-completed moment proof.
3. `SondowSymmetricSums.lean`: symmetric square sum split into the diagonal and twice one triangle.
4. `SondowFiniteEvaluation.lean`: evaluation of the entire truncated integral into harmonic numbers and finite logarithmic sums, using the previous moment and telescoping proofs.
5. `SondowBinomialCoefficients.lean`: reuses Mathlib's alternating binomial sum and Vandermonde square sum; derives the exact coefficient of log(N).
6. `SondowCutoffAlgebra.lean`: reindexes the triangle and boundary sum to match cutoffError, separates the logarithmic terms, and proves the signed-form identity and the exact conditional original statement.

`SondowLogMoment.lean` was refactored to export its existing integrability proof. The integration argument was not duplicated or weakened.

## Verification and platform state

Validation command: `lake build Solutions.SondowCutoffAlgebra`. The workspace enables `autoImplicit=false`. Axiom checks are printed by the modules; the completed results contain no `sorryAx`. The conditional wrapper explicitly quantifies its remaining equality hypothesis, so its clean axiom report is not evidence that the hypothesis has been proved.

Final validation output is saved at `continuation/cutoff-algebra-local.log`. This continuation did not publish additional nodes or submit a new reduction.

The live platform open frontiers were refreshed during this continuation. `integral_identity` still has the finite-cutoff leaf; `scaled_integral_bounds` still has the Schoenfeld large-argument and Rosser finite-middle leaves. Platform version remains 0.10.3. Neither requested original target is complete.

## Next mathematical step

Prove equality of the signed and positive logarithmic forms, corresponding to Lemma 2 and Proposition 10 in the Appendix of [Sondow v2](https://arxiv.org/pdf/math/0209070). Then the exact finite-cutoff statement follows from the wrapper above and the existing accepted limit reductions close integral_identity.

An elementary candidate for formalizing the combinatorial core is the finite row identity

    sum_{j=0}^n (-1)^j choose(n,j)/(j-k)
      = (-1)^k choose(n,k) (H_k-H_{n-k}),  0 <= k <= n,

with the j=k term interpreted as zero. Summing its row differences gives the cumulative rectangle identity in Proposition 10. Pascal recurrence reduces interior rows from n to n-1; the boundary row uses the alternating reciprocal-binomial sum. This is a proposed implementation route, not a proved Lean result. Check signs, endpoint cases and the source Appendix before implementing it.

The scaled-bound objective remains intact. The completed integral estimate is reusable, but this continuation does not establish the effective prime estimate required for d(2n)<8^n. The full two-target goal remains active.
