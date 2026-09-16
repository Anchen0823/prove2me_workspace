# Five-Primes Mission: Proof Implementation

Last updated: 2026-09-13 (Asia/Shanghai).

Latest: the concrete Type I analytic sum estimate is now proved with exact
`96/pi^2`, without an assumed variation or decay bound. Sixteen modules
pass in 19.662 seconds without `sorryAx`. The main remaining analytic task
is Type II; Vaughan identification and final assembly are also outstanding.
The goal remains active: complete both types, submit, then Git.
See [Type II work plan](typeII-work-plan.md). Older progress entries below
are chronological and are superseded where they list Type I analytic gaps.

Latest Type II continuation proves stronger unit spacing, an integer-grid
Hilbert eigenvalue bound of 7/2, and the cosecant kernel approximation.
Twenty modules check in 21.406 seconds without `sorryAx`. Conversion to the
matrix/quadratic-form estimate and the full Type II bound remain unproved.
The active goal is unchanged; no new submission or Git action has occurred.

Current active scope: the user's continued request to resolve
`theorem51_unit_numerator_bound`. Eleven auxiliary modules now pass the
combined check (18.362 seconds, no `sorryAx`), including the exact odd Fourier
bridge, log-product calculus, and a bounded-variation transfer theorem.
The actual piecewise slope still needs to be connected to its variation
budget, and the sharp Type II estimate remains missing. No new platform
submission was made. See [current proof progress](theorem51-progress.md).
The chronological entries below retain earlier mission work.

Latest goal continuation supersedes the preceding variation gap: the actual
zero-extended slope now has a complete variation bound, with all three jumps
included, and the actual amplitude is continuous. Fourteen modules pass the
joint Lean check in 18.790 seconds without `sorryAx`. Its integral increment
identity and discrete/Type I assembly remain, together with the Type II
estimate. The goal is still to finish both, submit to the platform, then Git.

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

## Explicit new request: large-q envelope

The user requested TaoFivePrimes.exp_sum_estimate_large_q_unit_source_envelope
as a new, bounded task after stopping the earlier run. Its verified proof
sketch is submitted as 308e42ec-6604-4445-8b66-e021c99c18bb; latest status
PENDING. It uses existing Open modulus transfer plus the new general
Theorem 5.1 input e1794571-24bf-41f1-8f08-9296fbea9a90 (Open). The proof
itself handles q0=0 and the logarithm specialization. See large-q-work-plan.md.
Follow only this submission to completion; do not resume unrestricted work.

### Large-q result confirmed

Submission 308e42ec-6604-4445-8b66-e021c99c18bb is SKETCH_ACCEPTED,
with no error message. The target remains Open with two Open analytic
inputs: theorem51_unit_numerator_bound and
small_q_modulus_transfer_source_envelope. Its decomposition was checked
on the server. The requested scoped contribution is finished; no new
target work or automatic Git push follows. See large-q-work-plan.md.

### Rosser timeout repaired on explicit user request

The user supplied the Rosser 300-second timeout screenshot. The replacement
submission `11751692-de02-4b67-8b2f-44fe1593d392` is now `SKETCH_ACCEPTED`,
with no server error. Local checking of the exact submitted file dropped
from the prior 227.327 seconds to 77.237 seconds after balancing interval
cases and removing unused work. The target remains Open with exactly two
Open inputs: `schoenfeld_psi_error_large` and `rosser_psi_finite_middle`.
The timeout repair is complete; unrestricted mission work is not resumed.
See [the repair record](rosser-timeout-fix.md).

## Explicit request: resolve large-q dependencies

The modulus-transfer child is now **Proved**. Complete proof submission
`26fa51c0-287c-4b4b-a6b8-3ac048574313` is **ACCEPTED**. It proves the stronger
constant 18 and uses no Open theorem assumptions. The large-q parent remains
Open with one Open theorem child, `theorem51_unit_numerator_bound`.

A local auxiliary proof of the centered Vaughan coefficient bound also passes
Lean checking. The explicit Type I/II estimates are not yet proved, and no
submission for that remaining dependency has been made. See
[dependency resolution](dependency-resolution.md) for evidence and the exact
remaining analytic work. This does not change the unrelated Rosser result.

## Remaining Theorem 5.1: subsequent proof attempt

The exact real-cutoff centered Vaughan identities, their restriction to
w > V, the half-log support bound, a valid sine lower envelope, and the
Type II algebra/constant rounding now pass local Lean checking. A specific
intermediate sine comparison in the cited paper fails even for permitted
parameters; a checked local replacement is available. This is not a disproof
of Theorem 5.1.

The explicit smoothed Type I estimate and the sharp bilinear large-sieve
estimate remain missing. The target is still Open; no new proof/sketch was
submitted. The current work has no software or authentication blocker.
See [Theorem 5.1 progress](theorem51-progress.md), with reproducible checks.

## Further continuation: corrected Type I sum proved

The odd-index trigonometric sum is now proved for both unit numerator signs,
retaining the target's exact `96/pi^2` coefficient after Fourier decay.
The finite-support Fourier second-difference bound, conditional Type I
assembly, and actual cutoff amplitude's finite support are also checked.
The expanded eight-module check passed in 18.343 seconds without `sorryAx`.

The amplitude's second-difference total estimate and the sharp Type II
large-sieve estimate remain unproved. The target is not solved, and no new
platform submission has been made. The current entry point remains
[Theorem 5.1 progress](theorem51-progress.md); earlier Type I gap descriptions
are superseded by that document's narrower remaining obligations.

## Submission cadence correction (2026-09-13)

The user explicitly requested incremental platform submissions rather than
waiting for the whole Type II proof. The previous all-at-once submission
gate is superseded. Publish substantive verified intermediate results,
then connect them through genuine reductions; do not count disconnected
auxiliary theorems as resolved leaves of the mission tree.

New local results: the integer Hilbert quadratic-form and double-sum bounds
with constant 7/2, a general Hermitian spectral bound, and the off-diagonal
bounded-kernel error estimate. The combined 23-module check passed in
23.634 seconds, with no sorryAx.

Published intermediate theorem: TaoFivePrimes.integer_hilbert_sum_bound,
16161f30-78e9-4015-90f7-d191d003f4ed. Full proof submitted as
ebc80926-623c-4483-aa9f-2178d3505ef9.
Current evidence is verification/integer-hilbert-verdict.json.
The theorem is not yet connected to the mission dependency graph. The
original theorem51 target remains Open. Next priority is a meaningful
Type I / Type II / Vaughan reduction that exposes and reuses proved work.

Server verification completed: submission
`ebc80926-623c-4483-aa9f-2178d3505ef9` is ACCEPTED, with empty error message.
The intermediate theorem `TaoFivePrimes.integer_hilbert_sum_bound` is now
Proved. This is a complete independent intermediate proof; it is not yet a
resolved leaf in the original mission tree, because the connecting Type II
reduction has not been submitted. No claim is made that theorem51 is solved.

## Theorem 5.1 decomposition interface (2026-09-13)

The public sums interface is published as definition
0638cceb-6d09-4432-b62a-48c625773961. It contains only definitions of the
positive odd divisor set, actual Type I sum, centered coefficient, and
actual Type II sum.

The three child publication jobs are recorded in
verification/theorem51-children-publish-response.json. The Type I interface
and self-contained proof compile (18.706 seconds; no sorryAx), as does the
exact-parent three-child reduction. The latter is only a reduction and has
explicit Open Vaughan and Type II dependencies.

Run scripts/submit_theorem51_reduction.ps1 -Part typeI or -Part parent only
after the existing jobs publish. The script checks current target status,
exact signatures, and local proof hashes, and guards against duplicate or
uncertain submissions. Do not create replacement jobs just because the
queue is slow. Consult the matching verification/*-verdict.json files for
server outcomes. This supersedes earlier all-at-once submission instructions.

The three child nodes are now published:
- Vaughan: 197dea21-9471-497e-ba7a-3372b3e6eab7.
- Type I: d0fdae67-dec9-4bf7-9f8e-7772e9446b85.
- Type II: 605a083b-e6e1-4471-b532-c6f34ea1a76a.

The Type I complete proof was submitted as
 a4144d51-5149-4860-b501-1c52d5cf290d.
The exact-parent reduction was submitted as
 5bd1af4a-f623-40c7-9293-b97b334da035.
Poll these same submission ids; do not submit duplicates. The combined
24-module auxiliary check passes in 21.731 seconds, without sorryAx.
No Git action has been performed: full Type II and Vaughan closure remain
required by the active goal. Incremental submissions do not redefine that goal.

Parent reduction ACCEPTED AS SKETCH:
`5bd1af4a-f623-40c7-9293-b97b334da035` is SKETCH_ACCEPTED with no error.
A fresh /decompositions read confirms all three new theorem children are
connected to the original theorem51 target. Evidence:
research/theorem51-decompositions-connected.json.
Type I proof verification is still pending at this snapshot; do not infer
its acceptance from the parent's sketch verdict.

## Verified connected Type I completion

Type I submission `a4144d51-5149-4860-b501-1c52d5cf290d` is ACCEPTED with
an empty error message. Together with the accepted parent sketch
`5bd1af4a-f623-40c7-9293-b97b334da035`, this closes the Type I leaf in the
original theorem51 dependency tree. The remaining children are the actual
Vaughan decomposition and centered Type II estimate. The whole target and
active goal are not complete. No proof job remains pending for these two
submissions, and no Git commit has been made for this goal.

Next: work on the two named Open children and submit incremental reductions
that reuse the existing proved Type I and integer Hilbert results. Preserve
the full goal: Type I and II plus platform completion followed by Git.

## Type II sine-kernel connection (2026-09-13)

New checked files:
- Theorem51KernelConstants.lean proves the short-arc condition from
  h <= (q+1)/q^2, q >= 100 and |j-k| <= q/2, and proves
  1 + (7/2)/(pi*h) + q/2 <= 2*q from h >= (q-1)/q^2.
- Theorem51CosecantForm.lean combines the integer Hilbert inequality and
  bounded-kernel error into an actual cosecant quadratic-form bound. On a
  half-modulus block with card-1 <= q/2, its coefficient is at most 2*q-1.
  The difference of two unit-phase conjugates divided by 2i obeys the same
  estimate. No cosecant quadratic-form bound is assumed.

The next concrete missing step is the finite geometric-sum Gram identity.
For an interval containing N integer indices, express the off-diagonal
kernel as the difference of two phase-conjugated cosecant forms divided by
2i (up to a harmless sign). The diagonal contributes N times the energy;
N <= interval_length+1 then gives interval_length+2*q. This must be proved,
not inferred merely from the cosecant estimate. Afterward, connect the
bilinear block/subdivision/counting and scale integration to the existing
Open Type II node 605a083b-e6e1-4471-b532-c6f34ea1a76a.

The original parent sketch and Type I proof remain accepted. This turn
adds local Type II proof infrastructure but no new platform submission.
Vaughan and Type II remain Open, and the goal remains active; Git is not due
until the requested full proof/submission end state is achieved.

## Actual finite exponential-sum bound (2026-09-13)

Theorem51GeometricKernel.lean now proves the angular character identities,
the finite geometric-sum/cosecant identity (including N=0), and the finite
Gram expansion. Theorem51FiniteLargeSieve.lean uses these identities and the
proved cosecant bound to establish the actual exponential-sum estimate:

sum_{j<N} |sum_m exp(-2*pi*i*j*h*idx_m) x_m|^2
  <= (N+2*q-1) * sum_m |x_m|^2.

Assumptions: q>=100, (q-1)/q^2<=h<=(q+1)/q^2, injective integer indices,
pairwise index distance<=q/2, and card-1<=q/2. The translated version permits
j+t for arbitrary real t without changing the coefficient. These results
assume neither a Gram bound nor a geometric-kernel estimate.

Next steps: discharge the block cardinality bound from integer spacing,
convert odd d and w interval sums to this row/column convention (including
phase sign), apply bilinear Cauchy--Schwarz and subdivision, then prove the
scale-integral estimate. N<=interval_length+1 yields the required coefficient
interval_length+2*q. The original connected Type II leaf is still Open.
No new platform mutation or Git operation was made in this continuation.

## Bilinear blocks and exact odd counting (2026-09-13)

Theorem51BlockCounting.lean proves integer_index_card_le, eliminating the
separate cardinality hypothesis of the finite large sieve. It also proves
that odd integers in [A,B] have cardinality at most (B-A)/2+1, including the
empty-set case.

Theorem51BilinearBlock.lean proves the actual single-block bilinear bound
and its finite-block subdivision version by two applications of
Cauchy--Schwarz. The subdivision conclusion retains exactly the factor
card(blocks) * (N+2q-1) * total_column_energy * row_energy. The column index
type is currently uniform across blocks (zero padding is available).

Theorem51TypeIICounts.lean proves the odd row count <=1.1*W/4 for W>=40,
the odd column count <=1.1*x/(4W) for x/W>=40, and the exact 1.1/8 square-root
prefactor when the row coefficients have the half-log-square budget.

The actual odd d,w interval partition, row/column phase normalization,
Mobius and centered-coefficient energy instantiation, and scale integration
are still outstanding. Do not claim that the Open Type II leaf is solved
from these generic block estimates. Next work should implement that concrete
reindexing and subdivision rather than reproving the Hilbert or sine kernel.
The platform Type I proof and parent sketch remain accepted; no new platform
submission or Git operation was made in this continuation.

## Actual odd-row and coefficient interfaces (2026-09-13)

Theorem51OddBilinearPhase.lean proves the positive angular-frequency version
by conjugation and the exact e(alpha*d*w) phase identity for d=2m+1 and
w=2(j+t). unit_odd_bilinear_block applies the bound to that literal kernel
when 4*alpha lies in the positive unit window.

Theorem51OddRows.lean reindexes the image of an integer interval under
n -> 2n+1 into a finite range, including the empty interval. Its theorem
unit_odd_rectangle bounds the literal sum over those odd w, with the exact
row cardinality in the large-sieve factor and in the coefficient energy.

Theorem51CoefficientEnergy.lean proves the half-log and squared-energy
bounds for theorem51Centered (the exact coefficient of the public Type II
interface), and the finite squared-energy bound for Mobius coefficients.

Still missing: the actual d-column partition and zero-padding/reindexing,
instantiation of integer coefficients via positive natural arguments,
negative-alpha normalization, and the scale integral. A concrete partition
route is to use half-index endpoints L=ceil((x/(2W)-1)/2), R=floor((x/W-1)/2)
and integer block size M=ceil(q/2). Block width M-1<=q/2, and for a nonempty
column interval, K=floor((R-L)/M)+1 satisfies K<=x/(2Wq)+1. Use zero padding
only beyond R and outside d>U; prove that it preserves the actual sum and
energy. Do not replace the concrete partition with an assumed block estimate.

No new platform submission or Git action in this continuation. Type I and
the parent reduction remain accepted; Vaughan and Type II remain unresolved.

## Concrete column subdivision (2026-09-13)

Theorem51ColumnPartition.lean proves consecutive range-block enumeration,
zero-padding invariance, exact integer-interval subdivision, and preservation
of the coefficient squared energy. It proves coverage by
K=(u-l).toNat/M+1 for M>0 and the quantitative block-count bound from the
real span and M>=q/2. half_modulus_block_size provides both size inequalities
for M=(q+1)/2 with natural q. Empty intervals are handled by zero padding.

Theorem51PaddedRectangle.lean now applies those exact identities to the
literal odd-row/odd-column expCircle kernel. unit_padded_odd_rectangle
bounds the original integer-column interval, without assuming that an
external decomposition exists or that padded energy is preserved. The only
partition inputs are its actual K,M, coverage, and half-modulus size bound;
all sum and energy identities are proved internally.

Next instantiate L,R,l,u using the ceil/floor half-index endpoints for
[x/(2W),x/W] and [W/2,W], choose M=(q+1)/2, and prove the desired K bound.
Use coefficient masks for d>U and w>V. Establish positive arguments before
casting the actual centered and Mobius coefficients through Int.toNat.
This should produce the concrete scale-W bound with prefactor 1.1/8;
negative-alpha normalization and the scale integral are still needed.
No new platform submission or Git action was made in this continuation.

## Concrete positive-frequency scale estimate (2026-09-13)

Theorem51ScaleIntervals.lean proves the ceil/floor odd interval interfaces,
row and column counts, and K <= x/(2Wq)+1 for M=(q+1)/2.
Theorem51ScaleCoefficients.lean defines the actual cutoff-masked Mobius and
public centered coefficients, and proves their squared-energy bounds.
Theorem51ScaleBound.lean now combines the exact padded rectangle with these
counts and energies. theorem51_scale_bound_positive proves

  norm(theorem51ScaleSum x alpha U V W)
    <= (1.1/8) * sqrt((W/4+2q)*(x/(2Wq)+1)*x) * log W

for q>=100, W>=40, x/W>=40 and the positive unit frequency window for 4*alpha.
The scale sum has the literal expCircle(alpha*d*w) kernel and actual d>U,
w>V masks; it assumes no coefficient-energy or rectangle estimates.
The combined 39-module check passes without sorryAx. Evidence is in
verification/theorem51-progress-result.json and theorem51-progress.log.

Next: prove conjugation invariance for the real coefficients, obtain the
signed unit-numerator version, and expose the scale-sum definition for a
connected Type II reduction. The scale-integral identity/interchange and
its explicit integral estimate remain to be formalized. Do not count this
local scale theorem as a platform-closed leaf. No platform submission or
Git commit was made in this continuation; the full goal remains active.

## Connected Type II scale leaf accepted (2026-09-13)

The actual signed scale estimate is now a proved child of the original Type II
node, not an isolated auxiliary theorem. The server decomposition was refreshed
and saved in research/typeII-decompositions-connected.json.

- Scale definition TaoFivePrimes_Theorem51Scale: published,
  7b97188e-8d91-404d-9639-ba742bc9e86b. It contains definitions only.
- TaoFivePrimes.theorem51_scale_bound_signed: Proved,
  b111b484-f725-4569-8504-3d222a36c577.
  Complete proof 01825288-444e-47ce-977d-b0f445697fa4: ACCEPTED.
- Existing Type II node 605a083b-e6e1-4471-b532-c6f34ea1a76a:
  sketch 13a21c90-5dd8-416e-82bb-7dc312825516: SKETCH_ACCEPTED.
- Its remaining child TaoFivePrimes.theorem51_typeII_of_scale_bound:
  b46d7b94-7c1d-4d9d-980f-18230c005f4c, Open.

The new reduction derives q>=100, W>=40 and x/W>=40 from the original
parameters for V<=W<=x/U, then supplies the proved pointwise bound to the
integration child. That child explicitly assumes only this pointwise bound
in addition to the original parameters; it still requires the eta_0 integral
bridge and the numerical integrated bound. The Type II parent is still Open.
Vaughan remains Open. Type I remains Proved. The full goal is not complete,
and no Git commit or push was performed.

Local additions: Theorem51ScaleSigned proves conjugation and both numerator
signs. Scale interval/coefficient/sum definitions moved into the public
Definitions/Def_TaoFivePrimes_Theorem51Scale.lean module; the proof modules
import it without duplicate definitions. The complete submitted leaf bundles
22 auxiliary proof modules and passes in 31.26 seconds without sorryAx.
The exact parent submission passes locally in 25.60 seconds as a reduction.

Further integration progress, not yet submitted: Theorem51ScaleIntegrals
proves integral(log(t)/t) = log(b/a)*log(a*b)/2 for 0<a<=b.
Theorem51ScaleSupport proves the actual scale sum vanishes for W<=V and,
when U,W>0, for x/U<=W. The combined 42-module check passes in 35.54 seconds,
without sorryAx. Existing cached example .olean files from before the public
-definition refactor may be stale: refresh their imports in dependency order
before standalone import checks, or use the combined checker.

Next work: prove the eta_0 scale identity and finite-sum/integral interchange
for theorem51ScaleSum, use the proved support restriction, then integrate the
coupled radical majorant and apply typeII_round_constants. Do not reprove the
finite Hilbert/large-sieve/scale analysis; it is now a closed platform leaf.

## Eta scale identity and finite Type II support (2026-09-13)

Theorem51EtaScale.lean proves eta0_log_overlap, including empty and touching
windows, then eta0_scale_integral over Icc(max(w,r/2), min(2w,r)).
scale_pair_mem converts this interval to the literal constraints
x/(2W)<=d<=x/W and W/2<=w<=W for positive d,w. The resulting theorem
eta0_pair_scale_integral proves the exact eta0(d*w/x)=4*integral pair-weight
identity. scale_pair_integrable proves integrability of that weight; the
complex-weighted and finite_eta0_scale_integral theorems justify finite
sum/integral interchange with arbitrary complex coefficients.

Theorem51TypeIIFinite.lean proves that the exact public Type II double tsum
is the norm of a finite double sum over 1<=d,w<=Nat.ceil(x), for x>0 and
U,V>=1. Terms outside this rectangle vanish because either a cutoff guard
fails or d*w/x>=1 and eta0 vanishes. The summand definition is identical
to the public Type II summand, including both coprimality conditions.

The combined 44-module check passes in 35.89 seconds without sorryAx.
No new platform submission or Git operation in this continuation. The last
platform state is unchanged: signed scale leaf Proved; integration reduction
and Vaughan Open; Type I Proved. The full goal remains active.

Next concrete connection: apply finite_eta0_scale_integral to the product
of the finite natural rectangles, with coefficient equal to the guarded
Mobius*centered*expCircle product. Prove the finite kernel sum equals
(theorem51ScaleSum x alpha U V W)/W on V<=W<=x/U by odd Nat/Int reindexing.
Outside that interval use the proved scale support and the strict U,V masks.
This will give the actual Type II scale-integral bridge; do not introduce it
as an assumed identity. Then use the integral norm inequality and integrate
the already proved coupled radical bound and log weight.

## Actual Type II scale-integral bridge proved (2026-09-13)

Theorem51FiniteScaleBridge.lean instantiates the pairwise eta0 integral for
the exact guarded Mobius*centered*expCircle coefficient. It proves global
integrability of the finite kernel, the exact public Type II integral
representation, and the integral norm inequality.

Theorem51NatOddReindex.lean proves a positive natural/odd integer interval
sum bijection. Theorem51ScaleReindex.lean applies it to both actual columns
and rows, proving theorem51NatScaleSum_eq. Theorem51ActualScaleKernel.lean
then proves the literal finite integral kernel equals theorem51ScaleSum/W,
including all cutoff and coprimality guards.

Theorem51ScaleIntegralBridge.lean proves support outside [V,x/U] vanishes,
and establishes the actual bridge

  theorem51TypeII x alpha U V
    <= 4 * integral_{V..x/U} norm(theorem51ScaleSum x alpha U V W)/W.

Its assumptions are only x>0, U>=1, V>=1, UV<=x. The accompanying theorem
theorem51_scale_weight_integrable proves interval integrability of the
actual norm-weighted scale function, needed for integral monotonicity.
These are proved identities/inequalities, not assumed interfaces.

Theorem51RootIntegrals.lean proves the exact integrals of 1/sqrt(t) and
1/(t*sqrt(t)), plus the weighted bounds, for 1<=a<=b:

  integral log(t)/sqrt(t) <= 2*sqrt(b)*log(b),
  integral log(t)/(t*sqrt(t)) <= (2/sqrt(a))*log(b).

Combined verification: 50 modules, 34.94 seconds, exit 0, no sorryAx.
No platform submission or Git operation was made in this continuation.
The accepted scale leaf and Type II sketch remain the latest publications;
the integration child and Vaughan are still Open. Full goal remains active.

Next: combine the proved scale hypothesis and typeII_radical_unit with the
actual integrable bridge. Rewrite its four roots as
A + B*sqrt(W) + C/sqrt(W), where
A=x/(2*sqrt(2)*sqrt(q))+sqrt(2)*x/sqrt(x/q),
B=sqrt(x)/2, C=x/sqrt(2). Integrate with integral_log_div_factorized and the
two new weighted bounds. Normalize sqrt(x)*sqrt(x/U)=x/sqrt(U), then use
already-proved typeII_round_constants for 0.1,0.39,0.55,0.78. Submit the
complete proof to b46d7b94-7c1d-4d9d-980f-18230c005f4c and verify cascade.

## Type I and Type II both Proved on Prove2Me (2026-09-13)

Integration proof f5179f27-fc47-4065-97d8-6db29f368927 is ACCEPTED.
The Type II parent 605a083b-e6e1-4471-b532-c6f34ea1a76a automatically became
Proved; Type I was independently refreshed and remains Proved. The original
Theorem 5.1 frontier now contains only Vaughan. Full mission completion is
not claimed. See typeI-typeII-platform-results.md for exact IDs and evidence.

The requested Git-after-platform milestone is now being performed for the
completed Type I/II estimates. Earlier notes postponing every Git action
until Vaughan closure were too broad; the broader dependency goal remains
active after recording this completed, separately verifiable milestone.

## Requested Type I/II goal completed and pushed (2026-09-13)

Both exact connected Type I and Type II targets are Proved, and integration
submission f5179f27-fc47-4065-97d8-6db29f368927 is ACCEPTED. Git commit
3b4d2f35afeb0155b74de1d0071b7cd49a47efb6 was pushed to origin/main and its
remote SHA verified through the GitHub API. Git connectivity was restored
by applying the already-enabled Windows proxy to that push only.

The explicit goal 'solve Type I and II, submit to the platform, then git' is
complete. This does not assert completion of Theorem 5.1 or the overall
five-primes mission: the separate Vaughan decomposition remains Open.
Earlier notes treating Vaughan closure as a prerequisite for this specific
Type I/II Git milestone overstated that goal's scope.
