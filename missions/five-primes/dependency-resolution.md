# Large-q dependency resolution

The explicit user request to solve dependencies resumes work on the two analytic children of `TaoFivePrimes.exp_sum_estimate_large_q_unit_source_envelope`. It does not resume unrelated Rosser or unrestricted mission work.

## Completed: modulus transfer

`TaoFivePrimes.small_q_modulus_transfer_source_envelope` (`cba0b2b8-5272-44e3-8764-6f3c559ebc64`) is **Proved**. Submission `26fa51c0-287c-4b4b-a6b8-3ac048574313` is **ACCEPTED**, with an empty error message.

The proof establishes the stronger constant 18 in place of 20.16. It imports only Mathlib and platform definitions, with no Open theorem assumptions and no `sorry`. The exact `theorem solution` signature was compared against the current target before submission. Local Lean checking with `autoImplicit=false` passed; the only warning concerns unnecessary tactic sequencing.

Files:
- `Solutions/Sol_TaoFivePrimes_small_q_modulus_transfer_source_envelope.lean`
- `missions/five-primes/modulus-transfer-explanation.md`
- `missions/five-primes/verification/modulus-transfer-local-result.json`
- `missions/five-primes/verification/modulus-transfer-verdict.json`
- `missions/five-primes/research/large-q-decompositions-after-transfer.json`

The large-q parent is still **Open**, with exactly one Open theorem child: `TaoFivePrimes.theorem51_unit_numerator_bound` (`e1794571-24bf-41f1-8f08-9296fbea9a90`).

## Remaining: explicit Theorem 5.1 estimates

Source: https://arxiv.org/html/1201.6656v4#S5 . The target combines the unit-numerator Type I alternative (5.7) with the Type II terms (5.5) and (5.6). Its constants and logarithmic powers must be retained.

The catalog's proved `Vaughan.typeI_bound` and `Vaughan.typeII_bound` quantify an unspecified positive constant. The latter also loses four logarithmic powers. Neither supplies the explicit constants in this target. The proved `AnalyticNT.Vaughan.vaughan_weighted_sum` is an algebraic identity, not the missing cancellation bound.

A faithful implementation still needs:

1. The modified Vaughan decomposition for the odd-supported cutoff, retaining the centered coefficient and its factor one-half.
2. An explicit Type I estimate for unit numerator with the stated coefficient 96 / pi^2. The cutoff has corners, so a smooth-function derivative argument needs either justified approximation or a bounded-variation formulation.
3. The explicit Type II bilinear estimate with coefficients 0.1, 0.39, 0.55, and 0.78, including the stated real cutoffs and logarithmic factors.
4. The triangle-inequality assembly of these estimates under the target's exact hypotheses.

`examples/five-primes/VaughanCenteredCoefficient.lean` develops the elementary coefficient bound. This auxiliary fact alone does not prove the Type II estimate. No replacement Open theorem was published to make the remaining obligation appear solved.

The next substantial proof work should target the modified Vaughan decomposition and the explicit exponential-sum estimates. Do not report the parent or this final dependency as proved until the analytic estimates have been checked.

The centered coefficient lemma passed local Lean checking with autoImplicit=false and no warnings (session 74210). Its exact file hash is recorded in verification/vaughan-centered-coefficient-local-result.json.

## Follow-up attempt on the remaining dependency

The user's follow-up "resolve it" triggered further work on Theorem 5.1.
Exact centered convolution identities, support lemmas, a corrected phase
comparison, and Type II radical/rounding inequalities are now locally checked.
The full target remains unproved and no new platform submission was made.
See [the detailed progress and source audit](theorem51-progress.md) and
`verification/theorem51-progress-result.json`. The audit disproves only an
intermediate source comparison, not the target theorem.

## Further continuation: Type I trigonometric step closed

The corrected odd-index trigonometric sum now has a complete Lean proof
for both numerator signs with the required constant `4/pi^2`, which yields
the target's `96/pi^2` after the Fourier-decay factor. A finite-support
second-difference Fourier estimate and a conditional Type I assembly are
also proved. The literal cutoff's piecewise formulas and amplitude finite
support are checked.

The expanded eight-module check passed in 18.343 seconds with no `sorryAx`.
The remaining Type I input is the actual amplitude's second-difference
total bound, plus the connection to the Vaughan sums. The sharp Type II
large-sieve estimate and scale integration are still missing. No new Open
theorem or platform submission was created during this continuation.

The next continuation also closed the exact odd-Fourier identification and
proved log-product derivative formulas, explicit curvature/jump budgets,
and a general transfer from bounded variation to finite sampled second
differences. Eleven modules passed the combined check in 18.362 seconds,
with no `sorryAx`. The actual piecewise slope's integral identity and
total-variation bound still need to be assembled from these components;
the full Type I and Type II estimates are not claimed proved.

Further goal work has now proved the actual zero-extended slope's variation
bound `48*log(4*d*r)/r`, including its three corner jumps. This closes the
variation assembly gap mentioned above. The integral increment identity and
passage to the integer second-difference sum are next; Type II remains open.
The fourteen-module check passes (18.790 seconds, no `sorryAx`). Platform
submission and the user-requested subsequent Git action have not occurred.

On 2026-09-13, the integral increment identity, full integer second-difference
bound, and actual Type I sum estimate were completed. `unit_typeI_actual_sum`
retains the exact `96/pi^2` and has no assumed analytic estimate. Sixteen
modules pass in 19.662 seconds without `sorryAx`. Type II and the final
Vaughan/target assembly remain. No platform submission or Git action yet.
