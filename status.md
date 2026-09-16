# Prove2Me Workspace Status

Last updated: 2026-09-17 (Asia/Shanghai)

## Current work

Active mission: **Every Odd Number Greater Than 1 is the Sum of at Most Five Primes**. See [the mission handoff](missions/five-primes/status.md).

Current phase: resolve the remaining Theorem 5.1 dependency of the accepted large-q sketch, on the user's explicit continuation request. The modulus-transfer dependency is already Proved. Local Type I calculus and bounded-variation work continues; the target is not yet proved. See [the current proof gap](missions/five-primes/theorem51-progress.md). The earlier Rosser timeout repair remains complete and is unrelated to this active task.

Write mathematical work, Lean code, and handoff documents in English. Report progress to the user in Chinese.

## Mission index

| Mission | Status | Handoff |
| --- | --- | --- |
| **Magic Squares I: MacMahon's Enumeration of Order-Three Magic Squares** | **Active.** 17 theorems Proved; 1 open child (`param_three_card`) before the goal auto-resolves. Mission proposal `In review`. | [Magic-squares handoff](missions/magic-squares/status.md) · [通俗说明](missions/magic-squares/intro.md) |
| Every Odd Number Greater Than 1 is the Sum of at Most Five Primes | Open; 13 frontier leaves on 2026-09-12; complementary correlation Proved, quadratic prime mass Open | [Five-primes handoff](missions/five-primes/status.md) |
| The Bunkbed Conjecture Is False | Root `Proved`; zero open leaves, verified 2026-09-12 | [Bunkbed archive](missions/bunkbed/status.md) |
| Weak Goldbach Conjecture — target `WeakGoldbach.verified_two_primes_4e14_to_4e18` | Target Open, reduced on 2026-09-15 to one Open sieve-coverage child | [Weak-Goldbach handoff](missions/weak-goldbach/status.md) |

## Start the next mission

1. Obtain the mission URL or ID from the user and inspect its current root, milestones, open frontier, and prior attempts using the project skill.
2. Check the target's `mathlib_rev` against the environment below. Use a separate checkout for a different environment; do not mix theorem mirrors from different environments here.
3. Create `missions/<slug>/status.md` from [the status template](missions/_template/status.md), and use `examples/<slug>/` for scratch Lean files.
4. Keep platform modules at `Definitions/Def_*.lean`, `Theorems/Thm_*.lean`, and `Solutions/Sol_*.lean`. These paths mirror server imports and are shared across missions in the same environment.
5. Save mission-specific explanations and verification responses under `missions/<slug>/`. Update this page to point to the active mission.

## Shared environment

- Lean: `leanprover/lean4:v4.33.1`.
- Mathlib revision: `0df444a360eaa60ab8c11dca51a86af692955474`.
- Keep `.lake/` to reuse installed dependencies and build artifacts.
- Follow [SKILL.md](SKILL.md) and [the mission solver workflow](references/mission_solver.md).
- `credentials.json` remains at the root and is gitignored. Never print or commit its contents; send credentials only to `https://prove2.me/api/v1`.

Local organization does not modify platform submissions or theorem status. The five-primes implementation phase has submitted two accepted proof sketches and one accepted complete proof; details are in its mission handoff.

## Latest scoped dependency work

The large-q modulus-transfer dependency is **Proved**, with complete proof
submission `26fa51c0-287c-4b4b-a6b8-3ac048574313` **ACCEPTED**. The large-q
parent remains Open with one analytic dependency: the explicit Theorem 5.1
unit-numerator bound. See [the dependency record](missions/five-primes/dependency-resolution.md).

The subsequent Theorem 5.1 work now also proves the corrected odd
trigonometric sum with the exact Type I constant, a discrete Fourier
second-difference estimate, and a conditional Type I assembly. All eight
auxiliary modules passed a combined Lean check in 18.343 seconds without
`sorryAx`. The concrete cutoff variation and sharp Type II large-sieve
estimates remain unproved; no new platform submission was made.
See [the current proof gap](missions/five-primes/theorem51-progress.md).

Further continuation adds the exact odd Fourier identification, log-product
derivatives, curvature/jump budgets, and a general bounded-variation to
second-difference transfer. The latest eleven-module check passed in 18.362
seconds without `sorryAx`. Connecting the concrete piecewise slope to these
results remains necessary; the target and Type II gap are not closed.

Active goal update: the actual zero-extended Type I slope variation is now
proved, including all three jumps. The real amplitude's continuity also
passes. The fourteen-module combined check took 18.790 seconds with no
`sorryAx`. Remaining work includes its integral increment identity, Type I
assembly, and Type II. The user requested platform submission followed by
Git; neither has occurred yet, and the goal remains active.

Latest: the concrete Type I analytic bound is now proved, including the
actual cutoff and exact `96/pi^2` constant. Sixteen modules check in 19.662
seconds without `sorryAx`. Remaining work is Type II, the Vaughan connection,
and final assembly/submission followed by Git. See
[Type II work plan](missions/five-primes/typeII-work-plan.md).

Type II continuation: stronger unit-phase spacing, the integer-grid Hilbert
eigenvalue constant 7/2, and a cosecant approximation error are now checked.
Twenty modules pass in 21.406 seconds with no `sorryAx`. The finite matrix
bound, full Type II estimate, final assembly, platform submission, and Git
remain outstanding. The detailed specialized route is in the Type II plan.

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

## Weak Goldbach target: one reduction submitted (2026-09-15)

Worked `WeakGoldbach.verified_two_primes_4e14_to_4e18`
(`24c6e94b-2b96-4f10-b16d-486fa48068eb`) in the Weak Goldbach Conjecture
mission (`570a7f0d`). The node is the Oliveira e Silva–Herzog–Pardi segment
of the verified binary Goldbach range above Richstein's 4·10^14; the mission
captain classifies it, correctly, as a verified-computation core.

Following the platform's own treatment of the sibling Richstein node, the
target was reduced to a single finite sieve-coverage obligation in the
published `GoldbachSieve` interface:

- New child `WeakGoldbach.verified_range_sieve_coverage` (`73e8ddac`),
  published: 4·10^12+1 blocks of 10^6 anchored at 4·10^14, small-prime bound
  9781, sieve cutoff 2·10^9.
- Reduction submission `7020cdba-e182-45ee-9d64-dd2512d4562c`:
  SKETCH_ACCEPTED, empty error message. The decomposition edge is registered;
  the target's only open leaf is now the new child.
- The submission inlines the sieve-soundness lemmas (survivor ⇒ prime,
  pairSums ⇒ Goldbach representation) and is sorry-free; local `lake build`
  passes and the submission's type was checked to be identical to the
  target's.

The target is NOT proved, and no arithmetic of the computation was verified.
Also added locally: mirrors of the `GoldbachSieve` definition, of the new
child, and of the target; scratch checks under `examples/weak-goldbach/`; and
`scripts/p2m_api.py` plus `scripts/submit_weak_goldbach_child.py`. No Git
commit was made in this turn. Details:
[Weak-Goldbach handoff](missions/weak-goldbach/status.md).

## New field: magic squares (2026-09-16 to 2026-09-17)

The user asked for a new formalization area from scratch. A catalog search
confirmed the platform had **no** magic-square content, so this is a
green-field build: definitions → structure → enumeration.

**Mission.** Proposal `c66f86f5-4921-40de-bce2-fb6564aebc67`,
*Magic Squares I: MacMahon's Enumeration of Order-Three Magic Squares*
(`ResearchPaper`, field Combinatorics). The user confirmed and submitted it on
2026-09-17; it is `In review`. Goal is
`MagicSquares.magic_count_three_divisible` with six milestones.

**Published definitions (3).** `MagicSquares` (`be2f2b6a`) — squares, the five
line sums, and the seven standard predicates plus the four counting functions
$H_n,M_n,P_n,S_n$; `MagicSquaresParam3` (`68eaae9b`) — MacMahon's order-three
parametrization; `MagicSquaresTransforms` — transpose, the two flips, and the
affine substitution with its exact line-sum identities.

**Proved theorems (17).** Eight structural facts from the first session
(centre identity, no normal square of order two, the magic constant
$2s=n(n^2+1)$, vanishing when $3\nmid t$, order-three constant 15 / centre 5 /
associative constant 10, panmagic ⇒ magic), then nine more: total sum equals
$n$ times the line sum; transpose and both flips preserve magicness; affine
substitution preserves it with $s\mapsto as+nb$; opposite cells of an order-three
square sum to twice the centre; the parametrization is sound; the
parametrization is complete; and — the hard one — the map
$M\mapsto(M_{00},M_{02})$ is a **bijection** onto the admissible parameter
pairs, so $M_3(3e)=\mathrm{paramCount}(e)$ (submission `2b7bc6bc`, ACCEPTED).

**Remaining.** One open child, `MagicSquares.param_three_card`
(`8063946a`): $\mathrm{paramCount}(e)=2e^2+2e+1$. The mathematics is settled
(fibre-wise in $a$: interval length $2a+1$ for $a\le e$ and $4e-2a+1$ for
$a\ge e$, giving $(e+1)^2+(e+1)^2-(2e+1)$); the work left is Lean engineering —
a `Finset.sigma` fibre decomposition and two finite sums. When it lands, the
goal auto-resolves, since the parent reduction `2e4cb80a` is already ACCEPTED.
`MagicSquares.semi_magic_count_three` ($H_3$) is untouched.

**Literature.** 11 papers under `referpaper/` (3.0 MB), listed in
[referpaper/README.md](referpaper/README.md): the counting line
(Beck–Cohen–Cuomo–Gribelyuk 2003 is the definitional baseline), the
construction line (Xin 2008, the direct source of the parametrization), and
three open-problem papers on squares of squares.

Details, node IDs, and the decomposition tree:
[magic-squares handoff](missions/magic-squares/status.md). A plain-language
walkthrough for a non-specialist reader is in
[magic-squares/intro.md](missions/magic-squares/intro.md).
