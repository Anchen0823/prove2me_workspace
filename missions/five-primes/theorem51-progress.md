# Theorem 5.1: verified progress and remaining gap

Target: `TaoFivePrimes.theorem51_unit_numerator_bound`, ID
`e1794571-24bf-41f1-8f08-9296fbea9a90`.

The target remains **Open**. No proof of its full conclusion and no new
platform submission have been produced in this attempt. The completed
modulus-transfer dependency remains Proved.

## Checked Lean results

`examples/five-primes/Theorem51VaughanIdentity.lean` proves the centered
Vaughan convolution identity with real cutoffs, identifies its divisor
coefficient, and proves a finite weighted version. It also proves the
restricted centered identity with the essential `w > V` restriction.
The half-log correction has `d <= UV` on the support `dw <= UV^2`.
These are exact algebraic statements, not exponential-sum estimates.

`examples/five-primes/Theorem51PhaseAudit.lean` proves the exact positive-unit
phase window and a valid sine lower envelope. It also proves a counterexample
to one intermediate comparison printed in the source. This is **not** a
disproof of the target theorem.

`examples/five-primes/Theorem51TypeIIAlgebra.lean` proves a coupled radical
inequality, derives the required scale relation from the unit-regime
hypotheses, and verifies rounding to 0.1, 0.39, 0.55, and 0.78. It does not
assume or prove a large-sieve estimate for the actual bilinear sum.

`Theorem51OddHarmonic.lean` proves the odd reciprocal-sum estimate and a
finite index-sum bound. `Theorem51TypeITrig.lean` combines them with a
quadratic sine envelope to prove the required trigonometric sum, including
both unit numerator signs. It retains the exact final coefficient `96/pi^2`.

`Theorem51DiscreteSecondDifference.lean` proves a finite-support Fourier
bound using the total norm of second differences. It requires no smoothness.
`Theorem51TypeIDiscreteAssembly.lean` uses this bound to control the sum of
the Type I term norms, conditional on an explicit amplitude-variation bound.
`Theorem51CutoffAmplitude.lean` proves the actual cutoff's piecewise logarithmic
formulas and finite support of its odd-lattice logarithmic amplitude.
The amplitude-variation bound itself is still unproved.

Run `./scripts/check_theorem51_progress.ps1` from the workspace root. It
combines all twenty files, checks them with `autoImplicit=false`, and prints
the axioms of the principal results. It records source hashes, elapsed time,
exit code, and a `sorryAx` check in
`verification/theorem51-progress-result.json`; compiler output is in
`verification/theorem51-progress.log`.

Latest combined check: exit code 0 in 21.406 seconds; no `sorryAx`.
Every printed principal result uses only `propext`, `Classical.choice`, and
`Quot.sound`. This checks auxiliary results, including a conditional assembly,
and must not be interpreted as checking the full target.

## Phase comparison requiring repair

Source: Tao, arXiv:1201.6656v4, Section 5.2, paragraph preceding (5.18),
https://arxiv.org/html/1201.6656v4#S5.SS2 . The PDF was also checked at
https://arxiv.org/pdf/1201.6656 .

At `q = 1602`, `beta = 0`, `alpha = 1/(4q)`, and `d = 1`, Lean proves

$$\sin(\pi/3204)<\sin(\pi/3202).$$

Thus the displayed comparison with denominator `q-1` has the wrong
direction in this case. The parameter choices `U=V=40`, `x=6400` meet the
target's size conditions. This prevents copying that intermediate step
verbatim; it does not imply that the final estimate is false.

The valid replacement proved locally is

$$\sin\left(2\pi d\frac{q-1}{4q^2}\right)
  \le \sin(2\pi d\alpha),\qquad 0\le d\le q-1.$$

The resulting odd-index trigonometric sum is now **proved** with the required
constant. For any finite set of positive odd indices `d < q`, and either
unit numerator sign, the checked result is

$$\sum_d \frac{d}{\sin^2(2\pi d\alpha)}
\le \frac{4}{\pi^2}q^2\log(4eq/\pi).$$

The target hypotheses imply `q >= 1602`. On `0 < t <= pi/2`, a quadratic
Taylor argument proves `csc(t)^2 <= 1/t^2 + 1`. The corrected phase envelope
then gives `d/sin(2*pi*d*alpha)^2 <= 0.41*q^2/d + d`.
The odd harmonic estimate `sum 1/d <= 1.5 + 0.5*log q`, the index-sum
bound `sum d <= q^2`, and `log q >= 6.5` provide sufficient numerical slack.
Multiplication by `24*log(4*x)/x` recovers the target's `96/pi^2` coefficient.
No stronger target hypothesis is needed for this trigonometric step.

## Discrete Type I reduction

For a finite-support sequence `F : Z -> C` and `|z| = 1`, `z != 1`, Lean
now proves

$$\left|\sum_n F(n)z^n\right|
\le \frac{\sum_n |F(n+2)-2F(n+1)+F(n)|}{|1-z|^2}.$$

For `z = exp(4*pi*i*d*alpha)`, the denominator is
`4*sin(2*pi*d*alpha)^2`. The conditional assembly consequently reduces
the remaining Type I estimate to

$$\sum_n |\Delta^2 F_d(n)| \le 96(d/x)\log(4x).$$

The concrete amplitude is
`F_d(n) = (log(2*n+1) + c*log d) * eta0(d*(2*n+1)/x)`.
Its finite support and cutoff formulas are proved. Establishing its variation
bound (with the appropriate coefficient restriction) and connecting the
Vaughan decomposition still require work. The odd exponential sum is now
identified exactly with the geometric Fourier series in
`Theorem51OddFourierBridge.lean`, including removal of its unit phase in norm.
The conditional theorem does not hide remaining obligations as imported Open
theorems.

## Subsequent continuation: calculus and variation transfer

`Theorem51AmplitudeCalculus.lean` proves the coefficient bound
`|log y + c log d| <= log x` when `d,y >= 1`, `dy <= x`, and `|c| <= 1`.
It identifies both actual logarithmic cutoff pieces with log products and
proves their first and second derivative formulas. It also checks the exact
endpoint/interior slope expressions with weights 16, 16, and 4.

Writing `r = x/d`, the checked curvature majorant is
`(4*log x + 11)/y^2`, conditional on the coefficient and cutoff-log bounds.
Its integral over `[r/4,r]` is `(12*log x + 33)/r`. The three jumps have norm
budget `36*log x/r`. Their sum is at most `48*log(4*x)/r`.
These component estimates have now been assembled into the actual piecewise
slope variation theorem described below.

`Theorem51VariationTransfer.lean` proves a general finite-sum transfer:
if a slope `g` has variation at most `V` and its step integrals give the
increments of `F`, the sum of norms of sampled second differences of `F`
at mesh width 2 is at most `2*V`. It uses Mathlib's `eVariationOn` and
interval integrals, so it does not require derivatives at the corners.

## Active goal continuation: actual slope variation closed

The user goal is to finish Type I and Type II, submit the resulting platform
proof, then perform the Git commit. The goal remains active. This continuation
made proof progress; there is no external blocker or live job left to poll.

`Theorem51VariationControl.lean` proves variable-derivative control of metric
variation, clamping and translation rules, finite addition budgets, the
variation of a single jump, and the exact decomposition of a zero-extended
two-piece slope into clamped pieces plus its three jumps.

`Theorem51SlopeVariation.lean` uses those results to prove the actual theorem
`typeI_piecewise_slope_variation`. For `r >= 4`, `d >= 1`, and `|c| <= 1`,
the explicitly defined slope is zero below `r/4`, the lower logarithmic
derivative on `[r/4,r/2)`, the upper derivative on `[r/2,r)`, and zero above
`r`. Its full variation on the real line satisfies

`eVariationOn (typeIPiecewiseSlope r d c) univ <= ofReal (48*log(4*d*r)/r)`.

This is a complete checked variation bound, not a variation hypothesis.
`Theorem51AmplitudePrimitive.lean` additionally proves continuity of `eta0`
and of the actual real-indexed amplitude `typeIRealAmplitude`.

## 2026-09-13: concrete Type I analytic estimate completed

`Theorem51AmplitudePrimitive.lean` now proves the right derivative at every
point, integrability of the piecewise slope on every compact interval, and
the exact integral increment identity. The proof includes all three corners.

`Theorem51ConcreteDifferences.lean` proves finite sampled bounds and passes
to the whole integer lattice by shifting the first potentially nonzero
second difference to index zero. Its theorem `typeI_actual_discrete_variation`
proves the previously assumed bound for the actual `typeIOddAmplitude`:

`sum_n norm(Delta^2 amplitude(n)) <= 96*log(4*x)/x*d`

under `d >= 1`, `4*d <= x`, and `norm c <= 1`.

`Theorem51TypeIActual.lean`, theorem `unit_typeI_actual_sum`, combines that
result with the exact odd Fourier bridge and the proved trigonometric sum.
It proves the full sum of norms of the actual odd-lattice inner exponential
sums over any finite set of positive odd `d <= UV`, with the target's exact
`96/pi^2` coefficient. It has no variation, decay, or smoothness hypothesis.
The sixteen-module combined check passed in 19.662 seconds with no `sorryAx`;
the actual Type I theorem uses only the three standard printed axioms.

The remaining work is the Vaughan-to-smoothed-sum decomposition/identification,
the Type II analytic estimate and scale integration, and final exact-type
assembly. No platform submission or Git commit has yet been made for this
goal. The next analytic focus is recorded in `typeII-work-plan.md`.

The next goal continuation proved stronger unit-phase spacing, an integer-grid
Hilbert eigenvalue bound `7/2` (including the inverse-square row bound), and
the cosecant approximation error needed for a specialized large-sieve route.
The full reused eigen-identity proof is locally checked with its license and
attribution preserved. These components do not yet prove the quadratic-form
or block exponential-sum bound. See the detailed next steps and provenance in
`typeII-work-plan.md`. The goal remains active; no submission or Git action.

## Type II algebra recovered in the target regime

Expanding the product inside the source's radical produces

$$\frac{x^2}{8q}+\frac{xW}{4}+\frac{x^2}{W}+2qx.$$

Termwise square-root subadditivity alone gives coefficient 1 on
`x / sqrt W`, not `1 / sqrt 2`. For this target, however,

$$x\le UV^2<qV\le qW.$$

The checked coupled-radical lemma uses this relation to justify the smaller
coefficient through a cross term. This establishes the needed algebraic
inequality in the unit regime, without claiming its validity for unrestricted
parameters.

## Exact remaining work

1. Connect the restricted convolution identity to the finite odd-supported
   smoothed sum and its Type I / Type II decomposition.
2. Instantiate the completed concrete Type I estimate with the coefficients
   and finite support supplied by the Vaughan decomposition.
3. Prove the separated-frequency bilinear large-sieve estimate with the
   required constants, then perform the scale integration.
4. Assemble an exact-type `theorem solution` and validate it before submission.

Catalog searches found no ready-to-use exact-constant result closing steps
2 or 3. The generic Vaughan bounds have unspecified constants. The inspected
Zeta23 Montgomery--Vaughan route gives a different constant (13 at the
eigenvalue-bound level) or assumes its Hilbert bound as a hypothesis; it is
not a direct substitute for the required sharp estimate.

There is no environment or authentication blocker. The unresolved issue is
the missing analytic proof. The source comparison audit, auxiliary identities,
and successful local checks do not close that gap.

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
