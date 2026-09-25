# Quadratic prime mass

Target: `TaoFivePrimes.eta1_quadratic_prime_mass`
(`f4cd87ed-a92c-4886-b0b7-e81a95dd0134`).

The target requires the sifted quadratic mass to differ from `(2/3)x`
by at most `x/75`. The exact cutoff energy `2/3` is already proved.

Source: Tao, [arXiv:1201.6656v4, Section 4](https://arxiv.org/html/1201.6656v4),
Lemmas 4.1 and 4.3. With the weight `eta1^2`, its total variation is 2,
its support lies in `[1/10, 9/10]`, and its supremum is 1. The source
estimates suggest the following two inputs:

1. The unsifted mass differs from `(2/3)x` by at most
   `x / (20 * log(x/10))`.
2. Sifting changes the mass by at most `2.52 * sqrt(x)`.

`PrimeMassReduction.lean` proves the numerical error budget and
normalization. Since `x >= 10^9` and `log(x/10) >= 7.5`, each error is
at most `x/150`. A conditional assembly lemma combines the two analytic
inputs; consult its verification record for the latest checked source.
Neither analytic input is asserted as proved.

The first input needs a precise Chebyshev error bound, not merely an
asymptotic prime number theorem. Tao invokes Schoenfeld, Theorem 7, to
bound `|psi(y)-y|` for `y >= 10^8`. Search the complete relevant platform
catalog and inspect that source before introducing a new dependency.
The `q=psi` search is noisy and paginated; the saved first page does not
establish absence. The Schoenfeld and prime-mass searches found no
ready-made version of the needed two-sided estimate.

The weight is piecewise polynomial, so the integration-by-parts bridge
must be proved on its pieces or via an absolutely continuous theorem;
the smooth hypothesis in the paper cannot simply be asserted.

The second input can follow the paper's prime-counting bound, or use a
weaker elementary sieve-loss estimate if it still fits the final error
budget. Check existing Mathlib prime-power sum identities first.

No new child theorem has been published for this reduction.

## Completed elementary sieve route

Use `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`, already proved in
Mathlib, rather than a separate prime-counting estimate. A weight bounded
between zero and one and vanishing for `n <= Nat.sqrt x` loses at most
`psi(x)-theta(x)` under the primorial sieve. Prime terms above that
threshold are coprime to the primorial; all remaining loss is bounded
by the unsifted nonprime mass.

`SieveLossNumeric.lean` has passed Lean and proves
`2*sqrt(x)*log(x) <= x/150` for `x >= 10^9`. The generic weighted
comparison and its cutoff specialization have passed Lean in `SieveLoss.lean` and `CutoffSieveLoss.lean`, with no warnings, no sorry, and no open theorem imports. The final theorem quadratic_sieve_loss bounds the actual target weight by x/150. Source hashes are recorded in verification/sieve-loss-result.json and verification/cutoff-sieve-loss-result.json.
This route uses a different error bound from the original `2.52*sqrt(x)`
and must be combined using the common final `x/150` budget.

## Piecewise Abel summation bridge

Mathlib's `sum_mul_eq_sub_sub_integral_mul` requires differentiability at
every point in the closed interval. Apply it to three separate global
polynomials on `[x/10,x/5]`, `[x/5,4*x/5]`, and `[4*x/5,9*x/10]`:
`(10*t/x-1)^2`, `1`, and `(9-10*t/x)^2`.

The corresponding natural summation intervals are left-open and
right-closed with floored endpoints. They partition the supported terms.
The two internal endpoint values equal 1; the two outer values equal 0.
Thus all boundary terms cancel when the identities are added.
After replacing `psi(t)` with `t + (psi(t)-t)`, polynomial integration
gives the main term `(2/3)x`. The error is bounded using the explicit
Chebyshev estimate on `[x/10,x]` and total derivative variation 2.

The primary Schoenfeld PDF was located at the AMS DOI
`10.1090/S0025-5718-1976-0457374-X`, but direct fetching returned HTTP 403.
The needed estimate is currently source-grounded through Tao's Lemma 4.3;
the original Theorem 7 has not yet been independently inspected.

Next: combine quadratic_sieve_loss with the normalization in PrimeMassReduction.lean, replacing its old 2.52*sqrt(x) hypothesis by the now-proved x/150 bound. Then implement the piecewise Abel bridge from an explicit Chebyshev-error hypothesis. No source theorem should be published until the bridge and the source statement are checked.

## Checked Abel identities and updated reduction

`PrimeMassReduction.quadratic_prime_mass_of_unsifted` now uses the
proved `quadratic_sieve_loss`; only the unsifted mass estimate is assumed.
The expanded file passes Lean and has a refreshed verification hash.

`QuadraticAbel.lean` proves the Abel formula for an arbitrary quadratic
weight `(A*t+B)^2`, with the cumulative von Mangoldt sum expressed as
`Chebyshev.psi`. It uses Mathlib's general Abel summation theorem and
proves the derivative and integrability hypotheses directly. The real
scalar-module instance conversion in `HasDerivAt.pow` needs `convert!`.

`TrapezoidAbel.lean` instantiates the ascending, constant, and descending
pieces and proves cancellation of all four boundary terms. Both complete
files passed Lean with `autoImplicit=false`; the quadratic file has one
style warning and the trapezoid file has no warnings. Hashes and logs are
in verification/quadratic-abel* and verification/trapezoid-abel*.

Remaining implementation steps:
1. Prove that the platform's finite sum with `eta1(n/x)^2` equals the three
   floored-interval sums in `trapezoid_piecewise_abel`. Include zero tails
   and endpoint conventions explicitly.
2. Split the resulting integrals into their polynomial main terms and
   error terms involving `psi(t)-t`. The main terms must total `(2/3)x`.
3. Bound the error integrals from a precisely stated two-sided Chebyshev
   estimate. `Chebyshev.psi_mono.intervalIntegrable` can supply local
   integrability; do not assume psi is continuous.
4. Resolve or publish the genuine explicit number-theoretic source only
   after checking its statement and the full reduction.

All compilation sessions from this update are terminal. No new server
submission or public child theorem was created.
## Platform weight-to-integral bridge completed

`CutoffPartition.lean` proves the exact three-piece formula for `eta1^2`,
including all endpoints and both zero tails. `FloorIntervalSum.lean`
proves the real/floored membership equivalence and the conversion from
range indicators to finite interval sums. Both files passed Lean.

`CutoffSumPartition.lean` proves `sampled_eta1_sq_partition` and then
`unsifted_quadratic_mass_abel`: the platform's actual finite weighted
von Mangoldt sum equals the two signed derivative-times-psi integrals
from `trapezoid_piecewise_abel`. This complete file passed Lean with
`autoImplicit=false`, no warnings, and no open theorem imports. Its
hash is in verification/cutoff-sum-partition-result.json.

The previously listed step 1 is now complete. Next, compute the two
polynomial main-term integrals after writing psi(t)=t+(psi(t)-t), and
bound the remaining error integrals using the precise source estimate.
The two main-term derivative integrals should be x/6 and -5*x/6,
respectively, giving a signed total of (2/3)x. These integral evaluations
and the source-error bridge are not yet proved in Lean.

Implementation note: rewrite equivalences inside conditional expressions
using `simp only`, rather than `rw`, to avoid a dependent Decidable
motive error. All compile sessions from this update have finished.
## Main term and error-transfer lemmas completed

`AbelMainTerm.lean` proves the general quadratic derivative moment and
`trapezoid_main_term`: the two signed polynomial integrals total `(2/3)x`.
`AbelKernelMass.lean` proves the general derivative integral and that the
ascending kernel and negative descending kernel each integrate to 1.
`AbelErrorBound.lean` proves `weighted_psi_error`, transferring a uniform
bound `|psi(t)-t| <= delta` through a continuous nonnegative kernel.
It obtains integrability from `Chebyshev.psi_mono`, without asserting
continuity of psi. All three complete files passed Lean with
`autoImplicit=false`, no warnings, and no open theorem imports.
Hashes are in verification/AbelMainTerm-result.json,
verification/AbelKernelMass-result.json, and
verification/AbelErrorBound-result.json.

Next assembly:
- Establish nonnegativity of the ascending kernel on `(x/10,x/5]`
  and of the negative descending kernel on `(4*x/5,9*x/10]`.
- Split each derivative-times-psi integral into its main term and its
  derivative-times-(psi-t) error. Use local integrability from psi_mono
  and polynomial continuity to justify integral_sub.
- Apply weighted_psi_error and trapezoid_kernel_integrals to bound each
  error by delta, then abs_add and trapezoid_main_term to get total 2*delta.
- Specialize delta=x/(40*log(x/10)) under the genuine pointwise source
  estimate, and invoke quadratic_prime_mass_of_unsifted.

The final assembly and the explicit Chebyshev source are still unproved.
No platform publication occurred in this update. All compile sessions
have finished.
## Conditional analytic reduction completed

`AbelErrorAssembly.lean` now proves `weighted_psi_difference` and
`unsifted_mass_error_of_uniform`. A uniform bound delta on psi(t)-t over
(x/10,9*x/10] gives absolute weighted mass error at most 2*delta.
Nonnegative kernels, integral subtraction, and signs are all proved.
The complete file passes Lean without warnings.

`QuadraticMassFromChebyshev.lean` proves `quadratic_mass_of_chebyshev_error`:
assuming the explicit source
`forall y >= 10^8, abs(psi(y)-y) <= y/(40*log y)`, the quadratic mass
conclusion follows under x>=10^9 and log(x/10)>=7.5. It uses log
monotonicity to obtain a uniform delta=x/(40*log(x/10)), then the
proved sieve loss and normalization. It passes Lean with one style
warning. The source hypothesis itself has NOT been proved or published.
Hashes and logs are in verification/abel-error-assembly* and
verification/quadratic-mass-from-chebyshev*.

Next: verify and locate the exact explicit Chebyshev source, check for
existing platform equivalents, and assemble an exact-target submission
only after determining the valid source dependency. The remaining target
hypotheses imply the two size/log conditions by arithmetic; retain the
platform's complete binder list in the final solution.

A potentially useful primary formalization project was found:
https://alexkontorovich.github.io/PrimeNumberTheoremAnd/blueprint/primary-chapter.html
Its primary and secondary explicit estimate chapters include Lean links.
The inspected chapter also has TODOs and unproved items; no needed
estimate has yet been verified there. Inspect exact source and transitive
axioms, not blueprint checkmarks alone, before reusing it. The secondary
chapter's Rosser-Schoenfeld bounds may also help another mission leaf.

All local compilation sessions are terminal. No new platform mutation
was performed in this update.
## Exact-target sketch prepared; source publication queued

The complete file Solutions/Sol_TaoFivePrimes_eta1_quadratic_prime_mass.lean
passed local Lean validation against the exact platform binder list.
See verification/mass-sketch-local-result.json for its hash. It imports
only one open source placeholder, schoenfeld_psi_error_large; the solution
body itself contains no sorry. The English explanation is
mass-sketch-explanation.md. The assembly script is
missions/five-primes/scripts/prepare_mass_sketch.ps1.

A fresh platform read confirmed the target Open and the matching
Mathlib revision. The Schoenfeld search found no equivalent source.
The source node has now been submitted for publication:
job 9d1e49ba-ffcf-4edd-9ef6-967edcfc42fc, latest status PENDING.
Response files: verification/chebyshev-source-publish-response.json and
verification/chebyshev-source-job.json. Do not publish it again.

Immediate next action: poll this exact job. Once PUBLISHED, save the
returned theorem_id, confirm its statement, verify the unchanged solution
hash, and submit the mass sketch to f4cd87ed-a92c-4886-b0b7-e81a95dd0134
with mass-sketch-explanation.md. Then poll the same submission ID to a
terminal verdict and inspect the updated dependency tree. No mass-sketch
proof submission has been made yet.

The new source remains mathematically Open even after publication.
External source audit and the unsuccessful complete-proof reuse paths
are documented in source-audit.md. All local Lean sessions have finished.
## Source published and mass sketch submitted

Publish job 9d1e49ba-ffcf-4edd-9ef6-967edcfc42fc is terminal PUBLISHED.
The new source theorem ID is 3fa7d8d1-e2ce-4057-894d-f39a2f0a4a8d,
name TaoFivePrimes.schoenfeld_psi_error_large. Its statement and environment
were checked against the reviewed payload. It remains mathematically Open.
The published record is research/chebyshev-source-published.json.

Submitted the locally checked exact-target mass reduction:
submission 22e9d559-4993-4086-b1e9-bc4fecf541fe, latest verdict PENDING.
Follow this same ID through GET /verify; do not submit again.
Response and verdict are verification/mass-sketch-submit-response.json
and verification/mass-sketch-verdict.json. The guarded submission helper
is missions/five-primes/scripts/submit_mass_after_source.ps1. It records an attempt before POST
and refuses an uncertain retry without inspecting server history.

Next: poll the existing proof submission to a terminal verdict. On
acceptance inspect the mass target, its decomposition, the original raw
major-arc target, and the mission root frontier. No claim that the source,
mass theorem, or mission is completely proved follows from a sketch verdict.
All local execution sessions in this update have finished.
## Mass sketch accepted; queue finished

Submission 22e9d559-4993-4086-b1e9-bc4fecf541fe is SKETCH_ACCEPTED,
with an empty error message. Its published decomposition contains ArcSplit
and only one Open theorem: schoenfeld_psi_error_large. The mass target and
root remain Open with 13 frontier leaves. All post-verdict snapshots are
in research/*after-mass-sketch.json and research/mass-after-sketch.json.
No submission is pending.

RosserLargeReduction.lean also passed local Lean checks without warnings.
It derives the strict large-argument bound psi(y)<1.03883*y from the same
explicit error estimate, and assembles a global integer bound conditional
on a finite certificate for 0<n<10^8. This is local groundwork only;
neither the finite certificate nor the explicit source is proved, and
no additional public decomposition was submitted. The verification
record is verification/rosser-large-reduction-result.json.

## Rosser finite-range interval scouting

RosserIntervalCover.lean passed Lean with autoImplicit=false and exit code 0.
It proves that endpoint certificates psi(b)<C*a cover every y in [a,b],
using monotonicity of psi and C>=0. Verification is recorded in
verification/rosser-interval-cover-result.json.

missions/five-primes/scripts/scout_rosser_intervals.py examined the range 1..99,999,999 in about
5.1 seconds. It found 2,152 covering intervals and no failed floating-point
endpoint comparisons. The smallest approximate gap was 0.0010647301683
at a=b=113. Full scouting data: research/rosser-interval-scout.json.
These are numerical observations, not formal endpoint certificates.
The finite-range theorem remains unproved. The next experiment replaces
the critical endpoint's floating-point logs by exact integer arithmetic
and a rigorously bounded logarithm series in Lean.

## Critical endpoint certified

RosserCriticalEndpoint.lean now passes Lean with autoImplicit=false,
exit code 0, and no warnings. It proves psi(113)<1.03883*113 from:
- the Mathlib identity psi(n)=log(lcmUpto(n));
- an exact lcmUpto(113) equality checked with kernel-reduced decide;
- the integer-checked upper bound lcmUpto(113)<=2^169*(159679/125000);
- explicit rational upper bounds log(2)<=0.693147181 and
  log(159679/125000)<=0.24485182, using the proven log series remainder.

The initial mantissa bound was too small and Lean rejected it. The corrected
rational bound passes. The LCM calculation uses maxRecDepth 4096 locally.
No native_decide, added axioms, open theorem imports, or floating-point
assumptions occur in this proof. See verification/rosser-critical-endpoint-result.json.

This certifies one endpoint, not the full finite range. All 2,152 endpoint
certificates (with efficient shared arithmetic) and the exact finite cover
still need formal assembly. The large-range explicit Chebyshev source
also remains Open. No new platform submission was made in this update.
All local Lean processes started for this update have terminated.

## Reusable integer certificates and a generated finite prefix

RosserLcmCertificate.lean passes Lean and is cached. It derives
psi(n)<=k*0.693147181 from lcmUpto(n)<=2^k, and the sharper
 d*psi(n)<=k*0.693147181 from lcmUpto(n)^d<=2^k.
It also proves an interval version and the endpoint n=1000.
See verification/rosser-lcm-certificate-result.json.

missions/five-primes/scripts/generate_rosser_prefix.py uses only exact Python integer arithmetic
to choose interval endpoints and powers. The generated Lean proof checks
all arithmetic with decide, all rational comparisons with norm_num, and
interval coverage with omega. Python itself is not trusted by the proof.
The prototype is intentionally bounded to 1..1000 pending performance data.
Its generated RosserFinite1000.lean has 87 blocks; the tight points
31, 32, and 113 use d=1000. This file is currently being checked in local
Lean execution session 80244; no validation verdict is recorded yet.
Do not claim the complete prefix or finite range proved before exit code 0.

## Complete 1..1000 prefix verified

The original RosserFinite1000.lean run (session 80244) finished with exit
code 0 and no warnings after approximately 278 seconds. It proves the
entire prefix 1<=n<=1000, not only the 87 endpoints. Its hash and precise
scope are in verification/rosser-finite1000-result.json. This still does
not prove the finite range through 99,999,999 or the large-argument source.

RosserLcmBlocks.lean also passed Lean and was cached. Its interval-splitting
identity lets each LCM certificate reuse the preceding exact value.
The generator now has --reuse-blocks; RosserFinite1000Blocks.lean is a
separate candidate using that optimization. Its validation is running in
session 63333. The process writes verification/rosser-finite1000-blocks-result.json
only on completion. No new platform proof was submitted.

## Incremental LCM version verified; power precision isolated

RosserFinite1000Blocks.lean passed with exit code 0, no warnings, and
213.8030886 seconds elapsed. The original version took about 278 seconds.
Both establish the same entire 1..1000 prefix. The separate interval-cover
proof passed in 30.7286847 seconds including startup/import time; this is
not a subtraction-based measurement of tactic time.

The generator now additionally supports --adaptive-powers and
--reuse-critical-proof. Adaptive powers reduce d=1000 to d=4 at 31 and
d=2 at 32. At 113 the compact candidate directly cites the previously
checked exact logarithm proof instead of evaluating a high integer power.
RosserCriticalEndpoint.lean was successfully compiled to an importable
cache. RosserFinite1000Compact.lean is generated and undergoing validation;
do not claim its performance or successful verification until its process
finishes. See verification/rosser-finite1000-compact-result.json when available.
No platform submission or theorem status change occurred in this update.

## Next contribution and stop boundary

Prepare the Rosser-Schoenfeld frontier reduction as the next substantive
submission. The exact target is TaoFivePrimes.rosser_schoenfeld_psi_bound
(cf6be7a8-2493-479a-9d57-6ee8535546d1). Split its integer range into:
1. 1..1000: supply the fully checked local certificate proof.
2. 1001..99,999,999: a genuine remaining finite certificate obligation.
3. >=10^8: derive the target from the already published Open source
   TaoFivePrimes.schoenfeld_psi_error_large.

First assemble and check the exact-target sketch locally, search for an
existing equivalent finite-range child, and refresh the target before any
publication. Only publish a new child if needed. The current finite-prefix
optimization is still running in session 84902; follow that same session.
Do not represent either the middle range or the explicit error source as
proved. After the next proof/sketch is submitted and its terminal verdict
is confirmed, stop autonomous mission work as requested by the user.

## Exact Rosser sketch checked; finite child publication queued

Solutions/Sol_TaoFivePrimes_rosser_schoenfeld_psi_bound.lean passed with
exit code 0, no warnings, and 227.3274341 seconds elapsed. Its exact hash
and scope are in verification/rosser-sketch-local-result.json. The file
imports only ArcSplit and the two genuinely Open theorem inputs; its own
code contains no sorry. The English explanation is rosser-sketch-explanation.md.

Fresh platform reads confirm the target is still Open in the pinned
Mathlib environment and has no proof decomposition beyond its definition.
The Rosser catalog search returned four entries and no finite-range child.
The new child publication is queued as job
2df28342-7b3c-4598-912e-53f9b05e044d, latest observed status PENDING.
Do not publish it again. See verification/rosser-middle-publish-response.json
and verification/rosser-middle-publish-job.json.

Next: run the guarded missions/five-primes/scripts/submit_rosser_after_middle.ps1 to inspect
that same job, check the published statement, and submit the verified
sketch once publication completes. Then follow the returned submission ID
to a terminal verdict, inspect the resulting decomposition, and STOP
mission work according to the user's requested boundary. No proof
submission has been sent yet in this contribution cycle. All local Lean
processes started for this cycle have terminated.
