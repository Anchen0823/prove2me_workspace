# Five-Primes Mission: Proof Implementation

Last updated: 2026-09-12 (Asia/Shanghai).

## Latest implementation update

Two accepted reductions now connect the raw major-arc L2 target to a
single explicit number-theoretic input; the complementary-correlation
child has a complete accepted proof.

- Raw reduction: SKETCH_ACCEPTED, 5af56872-532b-4db1-abca-5f501e5a52b9.
- Complementary correlation: ACCEPTED / Proved,
  bb88d850-1779-463a-9196-da6e7a951f88.
- Quadratic mass reduction: SKETCH_ACCEPTED,
  22e9d559-4993-4086-b1e9-bc4fecf541fe, empty error message.
- Sole open theorem input of the mass sketch:
  TaoFivePrimes.schoenfeld_psi_error_large,
  3fa7d8d1-e2ce-4057-894d-f39a2f0a4a8d.

Fresh API reads confirm the mass theorem and mission root remain Open,
with 13 frontier leaves. The old mass leaf has been replaced by the
explicit Chebyshev source. See research/mass-decompositions-after-sketch.json,
research/frontier-after-mass-sketch.json, and verification/mass-sketch-verdict.json.
No proof or publication job is pending; do not resubmit either contribution.

Next work: prove the genuine explicit Chebyshev source or advance another
remaining frontier. The checked RosserLargeReduction.lean shows the same
source suffices for the large-argument Rosser bound; a finite certificate
below 10^8 is still required. Neither input is claimed proved.
The interval-cover reduction is locally checked. Numerical scouting found
2,152 candidate intervals with positive approximate gaps, but their endpoint
bounds are not yet formal certificates. The tightest observed endpoint is 113.
RosserCriticalEndpoint.lean now proves this single endpoint using exact LCM
arithmetic and rational log-series bounds; it passed Lean without warnings.
The full prefix 1<=n<=1000 now passes Lean via 87 certified intervals
(RosserFinite1000.lean; verification/rosser-finite1000-result.json).
The remaining range 1001..99,999,999 is still open. Incremental LCM
certificates are being tested to reduce the roughly 278-second prefix cost.
See prime-mass-work-plan.md and source-audit.md for evidence and source limits.

## User objective and current phase

Continuously advance **Every Odd Number Greater Than 1 is the Sum of at Most Five Primes** until the user requests a stop. Submission `5af56872-532b-4db1-abca-5f501e5a52b9` is **SKETCH_ACCEPTED**, verified on 2026-09-12. The target and mission root remain Open. After the complementary-correlation proof, one analytic child remains Open and the mission has 13 frontier leaves. The sketch is an accepted reduction, not a complete proof of the target or mission.

Mathematical work, code, and documentation are in English. User-facing reports are in Chinese.

## Platform state verified during scouting

- Mission ID: `cdf62c01-8ad9-4eb0-bbcc-ef94ce25d4f8`.
- Root: `TaoFivePrimes.five_primes`.
- Root theorem ID: `59fb46ad-4ec0-4c68-9838-319eb070efdd`.
- Root status: `Open`; 13 open frontier leaves.
- Lean: `leanprover/lean4:v4.33.1`.
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`, matching this workspace.
- The root represents the primes as a multiset, allows repetitions, and requires cardinality at most five. It does not require exactly five primes.

The root and milestone data, selected theorem statement, and relevant discussion snapshots are in `research/`. Platform discussion descriptions of older frontiers are historical; the saved `/open-leaves` response is the scouting snapshot to use.

## Selected frontier target

`TaoFivePrimes.S1_major_arc_L2_mass_corollary49_raw`

- ID: `3c39e958-7602-4e59-bf6a-4ac45f8fb0a2`.
- Status: `Open`, closability score `0` when inspected.
- No submissions, proof decompositions, audit flags, or mentions were returned for this leaf. Its only listed dependency was the arc-split definition.
- The analytic milestone `300142e6-406f-4744-be09-e19412386242` had an empty edit history.
- This target contributes to the analytic branch; proving it alone will not close the mission.

With the explicit hypotheses in its formal statement, the target asks for a real error parameter satisfying

$$
|\varepsilon|\le 0.02,\qquad
0.999\,[0.99(1+\varepsilon)]^2x
\le \frac32\int_{\operatorname{majorArc}(x)}\|S_1(x,\alpha)\|^2\,d\alpha.
$$

It records the unrounded, correctly normalized specialization of Tao's Corollary 4.9 to the Section 8 cutoff.

## Mathematical route for the whole mission

Source: T. Tao, *Every odd number greater than 1 is the sum of at most five primes*, arXiv:1201.6656v4, https://arxiv.org/abs/1201.6656; especially Section 8, Theorems 8.1–8.2, and Corollary 4.9 in Section 4.

The paper splits the range into small numbers handled by explicit short-interval primes and verified binary Goldbach, a middle range from approximately `8.7e36` to `exp(3100)` handled by the circle method, and the large range handled by effective Vinogradov input. In the middle range, three odd primes sum to a number between `x-N0` and `x-2`, with `N0=4e14`. For odd `x`, the even remainder is between 2 and `N0`; remainder 2 is itself prime, and remainder at least 4 uses verified binary Goldbach. Thus at most five primes suffice.

The analytic argument expresses a nonnegative weighted representation count as a Fourier integral, splits the integral into major and minor arcs, and proves that the positive main contribution exceeds the possible minor-arc error. Both explicit pointwise bounds and integrated squared-norm bounds are required.

Large numerical verification leaves and effective external number-theoretic theorems remain real dependencies. A small contribution must not be reported as a complete formalization of Tao's theorem.

## Proposed proof route for the selected leaf

1. Fetch the exact platform definitions of `eta1`, `S1`, `majorArc`, and the smoothed exponential sums, including all transitive imports. Check existing platform and Mathlib results before creating any new public nodes.
2. Establish or reuse the cutoff's support, norm, and derivative/integral estimates. Normalize it as `sqrt(3/2) * eta1`, because its squared L2 norm is `2/3`.
3. Prove the needed smooth, normalized local L2 estimate using the prime-mass approximation and Fourier-tail estimates in Lemmas 4.1/4.3 and Proposition 4.8. Track the `0.02`, `0.01`, and `0.999` errors rather than replacing them with rounded constants too early. The existence of a ready-to-import general Corollary 4.9 theorem has not been established by this scouting pass.
4. Handle the literal piecewise-linear cutoff through a justified approximation/limit argument, or directly prove the corresponding bounded-variation estimates. Do not apply a smooth theorem to the nonsmooth cutoff without this bridge.
5. Use linearity of the smoothed sum and quadratic scaling of the integral to recover the factor `3/2` in the platform statement. Instantiate all explicit size/radius hypotheses without strengthening the target.
6. If the analytic inputs are too large for a direct proof, publish genuinely reusable, source-grounded child lemmas and submit a locally checked reduction. Do not replace the goal with an equivalent restatement called a source theorem.

## Source corrections and known pitfalls

The mission discussion records a normalization problem in the printed Section 8 L2 constants. Corollary 4.9 assumes L2 norm one, whereas equation (8.2) gives `||eta1||_2^2=2/3`. The corrected branch retains that factor; an unscaled lower bound such as `0.92*x` is not justified by the cited corollary. Relevant discussion IDs are `d2b62aaf-bbb4-491a-9332-1ec95df8d634` and `2acbd41e-8398-47ff-9acc-d4c777ef77c1`. This scouting pass confirmed the normalization statements against the original paper, but did not independently verify every revised constant in the discussion.

The modulus is a square-root primorial sieve, not coprimality to `x` itself. This removes prime powers from the weighted count. Existing asymptotic estimates cannot be silently substituted for the required explicit constants.

## Next action

Continue the quadratic prime mass route in prime-mass-work-plan.md. The complementary-correlation submission is terminal ACCEPTED and its tree update has been verified; do not resubmit it.

## Checked local progress

- Mirrored `ArcSplit`, `FourierRepresentation`, and `RepresentationCount` exactly from the saved platform catalog; `lake build Definitions.Def_TaoFivePrimes_ArcSplit` succeeded.
- `examples/five-primes/FourierMoments.lean` proves character orthogonality, finite Fourier correlation, Parseval, and the exact `S1` quadratic-mass identity.
- `examples/five-primes/LocalL2.lean` proves the continuous-function correlation inequality, localization with a complementary correlation bound, and the precise normalization arithmetic.
- Both files compiled successfully with `autoImplicit=false`, with no warnings in the final logs, no `sorry`, and no imported open theorem. See `verification/helpers-result.json` for source hashes and `verification/fourier-moments.log` / `verification/local-l2.log` for output.
- The detailed reduction and its three remaining estimates are in [major-arc-reduction.md](major-arc-reduction.md). These helper proofs do not yet establish the selected frontier theorem.
- No public comment, rating, proof submission, or theorem publication has been made for this mission.

## Subsequent cutoff progress

- `CutoffEnergy.lean` now proves the literal cutoff's piecewise formulas,
  continuity, bounds, exact squared integral `2/3`, and
  `sum eta1(n/x)^2 <= (2/3)x + 20` for every positive integer x. The full
  file compiled successfully without warnings and produced a local olean.
- `LocalL2.lean` additionally proves that the additive error 20 preserves
  the raw target's exact coefficient for `x >= 30000`. The target's `hc8`
  already gives `x >= 10^9`; no target hypothesis is strengthened.
- The original helpers-result hashes were refreshed for both files after
  successful compilation. The earlier text about three missing estimates
  is superseded: the cutoff-energy estimate is now proved, leaving two.
- Live `q=eta1` catalog inspection found no corresponding discrete energy
  theorem. The 47-result response is saved as `research/eta1-current.json`.
  Authentication refresh reported platform version `0.10.3`, matching the
  workspace skill. No platform mutation was performed.
- `MajorArcReduction.lean` subsequently compiled successfully. It proves
  the exact raw lower-bound conclusion from the two explicit analytic
  hypotheses, using the checked discrete energy bound. Only two
  `unnecessarySeqFocus` style warnings remain; there are no proof errors or
  `sorry` placeholders. Its source hash is in `helpers-result.json`.

## Publication and submitted reduction

- Fresh platform reads still showed the selected target Open, 13 frontier
  leaves, and the matching environment immediately before publication.
- Published `TaoFivePrimes.eta1_quadratic_prime_mass`:
  theorem ID `f4cd87ed-a92c-4886-b0b7-e81a95dd0134`,
  publish job `182d2359-60d0-4c0c-b35e-d19d808caa8b` (PUBLISHED).
- Published `TaoFivePrimes.eta1_complementary_correlation`:
  theorem ID `5f71df57-fdd6-4669-9e56-ce36eee723ce`,
  publish job `558a3fe9-9bac-420d-afa8-074a300b2d63` (PUBLISHED).
- Exact-target submission: `5af56872-532b-4db1-abca-5f501e5a52b9`.
  Final server status: **SKETCH_ACCEPTED**, with empty error message.
  The saved verdict is `verification/raw-sketch-verdict.json`.
  Source: `Solutions/Sol_TaoFivePrimes_S1_major_arc_L2_mass_corollary49_raw.lean`;
  explanation: `raw-sketch-explanation.md`. The complete file compiled
  locally, with only two style warnings and no `sorry` in its source.
- `scripts/prepare_five_primes_sketch.ps1` assembles that source from the
  checked scratch helpers and the exact target statement.
  `scripts/follow_five_primes_submission.ps1` tracks the existing jobs,
  guards against duplicate/uncertain submissions, checks the source hash,
  and polls the verdict. Response files are in `verification/`.
- While waiting, `FiniteDifference.lean` proved the finite-support Fourier
  shift/difference identities and the second-difference norm bound. Its
  verification hash is recorded separately. The concrete cutoff's hinge
  decomposition, second-difference nonnegativity, telescoping identity,
  and exact per-hinge total have also compiled in `CutoffDifferences.lean`.
  Its hash and scope are in `verification/cutoff-differences-result.json`.
- Post-acceptance API reads confirmed both named children in the selected
  target's actual decomposition. The target and mission root remain Open;
  the root frontier now has 14 leaves (one old leaf replaced by two).
  Authoritative snapshots: `research/decompositions-after-sketch.json`,
  `research/frontier-after-sketch.json`, `research/target-after-sketch.json`,
  and `research/root-after-sketch.json`.

## Checked Fourier-tail progress after sketch acceptance

- `CutoffDifferences.lean` now includes `eta1_second_difference_mass`:
  the sum of absolute forward second differences is at most `40/x`
  for `x >= 10`. This combines the four nonnegative hinge sequences.
- `CutoffFourierDecay.lean` defines the integer-indexed finite cutoff,
  proves its exact equality with the platform polynomial, proves all
  zero-extension and endpoint facts, and bounds its second-difference
  support. Its final result is `|1-e(alpha)|^2 |F_x(alpha)| <= 40/x`.
- `CircleTail.lean` proves the chord formula and lower bound, then
  `|F_x(t)| <= 5/(2*x*t^2)` for `0 < |t| <= 1/2`. It also proves
  the inverse-square integral on positive intervals.
- All three complete files compile with `autoImplicit=false` and no
  `sorry` or open theorem imports. The latest hashes and validation scope
  are in `verification/cutoff-fourier-decay-result.json` and
  `verification/circle-tail-result.json`; these supersede the older
  `cutoff-differences-result.json` hash for the expanded file.
- The full complementary integral and the prime-mass multiplication are
  still unproved. No new platform submission was made in this phase.

## User stop condition

The user requested on 2026-09-12: pause the ongoing mission goal when the
next platform contribution is formed. Operational interpretation communicated
to the user: finish the next substantive proof or proof-sketch submission,
confirm its terminal verification result, then stop autonomous mission work
and report the contribution and remaining dependencies. Do not continue to
another contribution after that boundary.

## Rosser sketch submitted; stop after terminal verdict

The finite child publication completed successfully. Its theorem ID is
d7089f63-d516-4c70-a5f5-f1ae1e917931, name
TaoFivePrimes.rosser_psi_finite_middle, status Open. Its statement and
Mathlib revision were checked before proof submission. The published
record is research/rosser-middle-published.json.

The verified Rosser sketch is submitted as
603f8cd6-63dc-4609-86ab-78ad326fcf66, latest verdict PENDING with empty
error text. See verification/rosser-sketch-submit-response.json and
verification/rosser-sketch-verdict.json. Do not submit again.

Next action: poll GET /verify?submission_id=603f8cd6-63dc-4609-86ab-78ad326fcf66.
After the terminal verdict, inspect the target decomposition and root
frontier, record the outcome, then stop autonomous mission work. The user
explicitly requested this stopping boundary. Do not start another proof.

## User-requested stopping boundary reached

The next platform contribution has been formed and submitted:
603f8cd6-63dc-4609-86ab-78ad326fcf66. The latest direct API check still
reports PENDING with an empty error message. The mission and Rosser
frontier are not claimed proved.

The user's exact instruction was to pause when the next platform
submission is formed. That condition has been met. Stop further proof
work and repeated polling now; the earlier plan to wait for a terminal
verdict extended that requested boundary. Resume only on an explicit
new user request. The available goal tool cannot set a paused status;
do not mark the mathematical mission complete to simulate a pause.
