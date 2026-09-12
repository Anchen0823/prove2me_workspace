# Type II: remaining exact analytic work

The concrete Type I bound is checked in `Theorem51TypeIActual.lean`.
The goal remains to prove the full Theorem 5.1 target, submit it, then Git.
Incremental submissions are now required by the user. A three-child reduction
exposes the Vaughan, Type I, and Type II obligations explicitly. An accepted
sketch is not a solution of its Open children. Type I has a complete local
proof; the other two obligations remain open.

## Source and required input

Tao, arXiv:1201.6656v4, Sections 3 and 5.3:
https://arxiv.org/html/1201.6656v4 . Re-read on 2026-09-13.
The source uses the sharp large sieve (Lemma 3.6), its bilinear and odd-index
specializations (Corollaries 3.7--3.8), and subdivision (Corollary 3.9).
The sharp input has constant interval length plus inverse frequency spacing.
An unspecified constant or an extra logarithmic loss does not suffice.

For a scale W in [V,x/U], the needed estimate after coefficient counting is

`F(W) <= (1.1/8)*sqrt((W/4+2*q)*(x/(2*W*q)+1)*x)*log W`.

Here F is the actual bilinear sum on odd d in [x/(2W),x/W] and odd w in
[W/2,W], with d>U, w>V, Mobius(d), and the centered Vaughan coefficient.
The required frequency spacing is at least 1/(2q). The already-proved
unit-regime coupled radical lemma handles the subsequent expansion without
repeating the source's invalid unrestricted termwise simplification.

## Implementation steps

1. Establish the sharp finite large-sieve input, or a specialized unit-phase
   estimate strong enough to imply the exact displayed F(W) bound. This is
   the main unproved analytic step. Odd reindexing, interval subdivision,
   and Cauchy--Schwarz must retain the precise constants.
2. Prove the odd interval counts and apply the centered coefficient estimate
   `|g(w)| <= log(w)/2`, using U,V >= 40 to justify the 1.1 factors.
3. Prove the scale decomposition of eta0 and bound the actual Type II sum by
   `4 * integral F(W)/W` over [V,x/U]. Handle support and integrability.
4. Integrate the scale bound. The logarithmic integral is
   `integral_V^(x/U) log(W)/W = (log(x/U)^2-log(V)^2)/2`.
   The source's display (5.19 onward) contains transcription/printing slips:
   do not copy the displayed unweighted integral as an identity. The mixed
   logarithm product comes from this weighted integral. Bound log(W) by
   log(x/U) for the two square-root terms. Use the checked rounding lemmas.
5. Connect the restricted Vaughan identity to the actual smoothed sum,
   instantiate the completed Type I estimate, then assemble `theorem solution`
   with the exact target type. Check locally, submit once, verify the result,
   and perform the requested Git action only afterward.

## Reuse search, 2026-09-13

Fresh platform searches are saved as `research/typeII-search-*.json`.
The exact phrase `large sieve` returned the Open minor-arc L2 node and the
proved `Vaughan.sum_mul_e_eq_bilin`, which is only an algebraic reindexing
identity. The inspected Zeta23 eigenvalue bound still has constant 13.
Broad `sieve` and `Selberg` searches return many unrelated entries and are
limited pages, not an exhaustive proof of absence. These searches have not
identified a ready-to-use sharp result. Do not repeat the same broad queries
without a new reason; focus on proving the missing finite estimate.

Authentication refresh succeeded with platform version 0.10.3. No platform
mutation was made. There is no external blocker, and no live job to poll.

## Subsequent progress: a specialized unit-phase route

The new route uses the unit numerator to leave room for a coarser Hilbert
constant, instead of formalizing the general sharp large sieve from scratch.
The following facts are now fully checked:

- `Theorem51TypeIISpacing.lean`: for q>=4 and 1<=j<=q/2, the distance of
  4*j*alpha to every integer is at least `(q-1)/q^2` in the positive-unit case.
  This is nearly 1/q, rather than the source's weaker 1/(2q).
- `Theorem51HilbertIdentity.lean`: locally checked, complete finite algebra
  proof of the Preissmann--Leveque eigen-identity. It is adapted only by
  renaming the final theorem from the accepted submission listed below.
- `Theorem51UniformHilbert.lean`: for an injective integer index family, the
  inverse-square row sum is <=4, and the skew Hilbert kernel's real eigenvalue
  parameter satisfies `abs mu <= 7/2` for a normalized eigenvector. The proof
  uses the identity and `2 Re(u_m conj u_n) <= norm(u_m)^2 + norm(u_n)^2`, giving
  `mu^2 <= 12`. There is no unproved row-sum assumption in the integer theorem.
- `Theorem51CosecantError.lean`: for `0<abs t<=8/5`,
  `abs(1/sin t - 1/t) <= 1`.

The 20-module combined check passes in 21.406 seconds without `sorryAx`.
The checker now isolates each source body in a section, so scoped Mobius
notation from the Vaughan file does not leak into eigenvalue binders.

### Next steps for the finite operator bound (still unproved)

1. Completed: convert `integer_hilbert_eigen_bound` to a quadratic-form bound for the
   finite Hermitian matrix `i/(idx m-idx n)`. Use Mathlib spectral decomposition;
   do not use `MV.mvDiag_of_eigenBound` directly, since its `EigenBound` requires
   all nonuniform weight families, whereas the new bound is an integer-grid
   specialization. A potential reusable spectral identity is the platform's
   `Zeta23.MV.star_dotProduct_mulVec_eq`, matching-revision ID
   `0cbd2473-a4cb-4713-90d9-b84ce0620ed6`; its proof was fetched and adapted
   to Mathlib's spectral theorem. The resulting integer Hilbert sum inequality
   is Proved on the platform (16161f30-78e9-4015-90f7-d191d003f4ed).
2. Put h=4*abs(alpha). In a q/2 index block, h>= (q-1)/q^2 and
   pi*h*abs(j-k)<=8/5 (q>=1602). Compare the cosecant kernel with
   `1/(pi*h*(j-k))`. The error matrix has entries bounded by 1, giving a
   quadratic-form error <=(block_card-1)*energy, with block_card-1<=q/2.
3. Expand the finite exponential Gram kernel using the geometric sum. Its
   off-diagonal part is the difference of two unit-phase conjugates of the
   cosecant form, with coefficient 1/2, so the same bound applies. Account
   for integer-point counting: it is enough to prove
   `1+(7/2)/(pi*h)+q/2 <= 2*q`. This has ample margin in the target regime,
   but its Lean proof and the matrix estimate are still outstanding.
4. This would give the needed block bound `interval_length+2*q`. Complete
   the odd reindexing, subdivision, counting, scale integration, and Vaughan
   assembly listed above. Neither the finite large-sieve estimate nor the
   complete Type II theorem has been proved yet.

### Reused proof provenance

Matching-revision eigen-identity theorem:
`32ec0da9-b9af-40b5-a23f-66e884bd5f50`, accepted submission
`e2c521f7-2d40-47aa-84b0-cd6cdb3872a6`.
Original source: https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/MV/EigenIdentity.lean .
The Apache 2.0 notice is preserved in the code, with a license copy in
`third-party/Apache-2.0.txt`. The full proof is included and checked locally;
there is no placeholder import. The duplicate theorem beginning `2af915bd`
uses another Mathlib revision and was not used for the local proof.

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
