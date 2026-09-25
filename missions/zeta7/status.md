# Zeta(7) irrationality: local research attempt

Date: 2026-09-24. Status: **planned attack executed; no proof of irrationality**.

Start with the latest [execution report in Chinese](research/round2-report-zh.md).
The layered and whole-shift search produced 188 successful records, and a
rank-derived fixed-degree branch produced another 36. All 222 zeta(7)
records are greater than one after primitive integer normalization; two
zeta(5) controls are below one. Counts include repeated controls. The two
K160 determinant calculations timed out at 120 seconds and remain unresolved.

New proved intermediate results include `degree(det(A+XB)) = rank(B)`, an
explicit constant-polynomial exclusion region, rational upper approximants,
and finite coefficientwise integerization certificates for all primes.
A 32-arc comparison measure has a certified global potential bound, using
312 middle intervals and both infinite tails; its shifted-factorial real
exponent bound is `U < 0.507`. Independent 256-bit replay passed. The missing
step remains a sufficiently strong uniform arithmetic growth bound and a
strictly negative combined exponent. No Lean irrationality proof was created.

## Earlier research and literature

Read [the Chinese research report](research/attempt-report-zh.md) first.
The subsequent [literature review](research/literature-review-zh.md) surveys
established results and candidate methods, with original sources and version checks.
The positive functional, moment and pole identities, determinant positivity,
and degree arguments extend to zeta(7). The final arithmetic-versus-real
decay inequality has not been closed.

Exact rational coefficients and Arb enclosures reproduce the zeta(5)
baseline and show primitive zeta(7) values greater than one for all 324
saved zeta(7) records (including repeated parameters). At K=40 and K=80
with the original ratios, log P(zeta(7)) is approximately 1227.12 and
5414.21. These are finite results, not a proof of asymptotic impossibility.

Exploratory searches varied zero multiplicities, cutoffs, matrix dimension,
and prime-range boundaries. The sampled potential and arithmetic integrals
are explicitly not certified bounds. Full coefficient artifacts, hashes,
strict evaluation intervals, and reproducible scripts are saved locally.

Source: `referpaper/ZETA5_IS_IRRATIONAL.pdf`, Aabir Fauzan, 17 September 2026.
The user's request is to attempt a mathematical proof by adapting this construction.
This workstream has no Prove2me mission or submission and makes no publication claim.

## Work allocation

- Main agent: analytic energy experiments, integration, independent checks, final report.
- `arithmetic` (GPT-6 Astra): general local valuation bounds and normalization cost.
- `exact_experiments` (GPT-6 Sol): exact rational determinant polynomials and finite experiments.
- `analytic_audit` (GPT-6 Sol): independently checked analytic foundations and proof obligations.

## Proof boundary

Positive moment identities and an irrationality criterion are intermediate facts.
Numerical decay, a fitted slope, and small examples do not prove an eventual bound.
The target remains integer polynomials of degree O(n), strictly positive at zeta(7),
with a rigorously established exp(-c n^2) upper bound for some c > 0.

Research and executable checks are stored in `research/`, `scripts/`, and `verification/`.
