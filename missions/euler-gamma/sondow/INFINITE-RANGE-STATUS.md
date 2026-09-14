# Infinite-range source and dependency status

## Source recovered from user upload

The user supplied `C:/Users/anche/Downloads/S0025-5718-1975-0457373-7.pdf`
(27 pages, SHA256 `D0CC914A4D19B2C113655BF0C0D0FF0E2EBA45F9728825EC7BE561D7A090817B`).
The prior source-access blocker below is historical and resolved. Printed pages
258, 265, 266 and 267 have been rendered and visually inspected. OCR confuses
theta with psi and drops equality signs; the page images are authoritative.

Theorem 7 applies at `x >= 10^8`, including equality, and gives the stronger
strict bound `0.0242269 * x / log x` for both theta and psi. Its proof uses the
error table up to `exp 1300`, then Theorem 2. Theorem 2 applies at `log x >= 105`;
equation (3.19) uses `X = sqrt(log x / R)`, `R = 9.645908801`, and
`epsilon = 0.257634 * (1 + 0.96642/X) * X^(3/4) * exp(-X)`.

### Simplification for the exact psi-only target

Equation (4.1) supplies `abs(psi x-x) < epsilon*x` for **all** `x >= exp b`.
Only three rows from printed page 267 suffice for our weaker coefficient 0.025:

| b | epsilon | use until log x | epsilon times upper endpoint |
|---|---|---|---|
| 18.42 | 0.0012015 | 20 | 0.02403 |
| 20 | 0.00065941 | 35 | 0.02307935 |
| 35 | 0.000018315 | 1300 | 0.0238095 |

All products are strictly below 1/40. The first row is applicable because
`log(10^8) > 18.42`. This removes the theta correction terms and the need to
reproduce every table row. It does not prove the analytic validity of any row.

The corresponding table parameters `(m, delta)` are `(2, 0.000269)`,
`(3, 0.0000847)`, and `(12, 0.00000273)`. Equation (4.2) sets
`T1 = delta^(-1) * (2*R_m(delta)/(2+m*delta))^(1/m)`; Section 4 uses
`T2 = 0` for these rows. These transcription details have been checked against
the page images and are not validated numerical certificates of equation (4.8).

### Actual analytic foundations still required

The table is generated from Theorem 4, equation (4.8), via Lemmas 8 and 9.
Lemma 8 uses the explicit formula from Rosser (1941), Theorem 13, and the
zero-free region from this paper's Theorem 1. Lemma 9 uses the bound (4.4)
on the reciprocal moduli of the first 57 zeros with `0 < gamma <= D = 158.84998`.
The introduction and Theorem 2 proof also use certified critical-line zeros
up to `A` (approximately 1894438.51224), with `N(A) = F(A) = 3502500`.
Those numerical statements are mathematical proof obligations, not axioms
that may be imported merely because the paper reports computations.

The threshold lemma `EulerMascheroni.Sondow.log_ge_table_start` has passed
local Lean checking in 59.8038862 seconds and a subsequent cached module build
in 55 seconds. Luna's `sondow_schoenfeld_three_rows` has passed its module
build in 30 seconds. Both report only `propext`, `Classical.choice`, and
`Quot.sound`. Source files are `Solutions/SondowSchoenfeldThreshold.lean`
and `Solutions/SondowSchoenfeldThreeRows.lean`. These are local verification
times, not platform submission results.

Terra's `sondow_schoenfeld_tail_numeric` in
`Solutions/SondowSchoenfeldTailNumeric.lean` now also has a successful local
module build (52 seconds) and exactly the same three standard axioms. It
proves `epsilon(t)*t < 0.025` for every `t >= 1300`, using `X >= 58/5`,
`X^(3/4) <= (3/5)*X`, a cubic-times-exponential bound, and a finite exponential
series lower bound `exp(58/5) > 105000`. Earlier drafts had compilation
errors; only the final exit-zero module build counts as successful validation.

The complete conditional assembly in `Solutions/SondowSchoenfeldAssembly.lean`
has now passed `lake build Solutions.SondowSchoenfeldAssembly`, exit 0,
with a 50-second module build (74.8729042 seconds total command wall time,
including dependency handling). All three assembly theorems report only
`propext`, `Classical.choice`, and `Quot.sound`. The final theorem
`EulerMascheroni.Sondow.psi_error_of_rs1975_estimates` has the exact original
conclusion for every `y >= 10^8`, conditional on the three table bounds and
the Theorem 2 bound; it introduces no hidden axioms. The build verifies the
imported numeric modules together with this assembly.

Analytic hypotheses must remain explicit until the foundations above are
proved. No claim of a complete infinite-range proof follows from these
numeric proofs, and no new Graph nodes or platform submissions were made.
Source hashes are saved in `continuation/rs1975-numeric-source-hashes.json`.

## Exact obligation

`TaoFivePrimes.schoenfeld_psi_error_large`, platform ID
`3fa7d8d1-e2ce-4057-894d-f39a2f0a4a8d`, requires

```text
For every real y >= 10^8,
abs (Chebyshev.psi y - y) <= y / (40 * Real.log y).
```

This obligation remains unproved. No new proof or graph decomposition was submitted in this continuation.

## Verified source identification

Tao, *Every odd number greater than 1 is the sum of at most five primes*,
arXiv:1201.6656v4, proof of Lemma 4.3, explicitly invokes reference [44],
Theorem 7. Reference [44] is J. B. Rosser and L. Schoenfeld,
*Sharper bounds for the Chebyshev functions theta(x) and psi(x)*,
Math. Comp. 29 (1975), 243-269, DOI 10.1090/S0025-5718-1975-0457373-7.
It is not the 1976 Part II paper. This corrects the source-search direction;
it does not supply a formal proof of Theorem 7.

Primary reference inspected:
https://arxiv.org/html/1201.6656v4#S4

AMS full text returned HTTP 403 / a non-retryable URL-access error.
The JSTOR article landing page yielded no mathematical text.
Consequently the proof of the original Theorem 7 has not yet been independently
inspected here, and its detailed dependency list is not asserted.

## Additional upstream audit

At pinned PrimeNumberTheoremAnd revision
`a5154676af9aa3095150ee410cdda80555aa0642`, the newly fetched
`IEANTN/RosserSchoenfeld/RosserSchoenfeldZeta.lean` contains only
`RS.theorem_19`, a Rosser 1941 zero-count estimate for T >= 1467.
Its proof is `sorry` at line 31. It is neither the needed Theorem 7 nor a
completed zero-count foundation to import.

Snapshot: `continuation/upstream-RosserSchoenfeldZeta.lean`.
Together with the earlier audits in `UPSTREAM-ERROR-BOUND-AUDIT.md`, this
rules out the specific inspected wrappers as complete dependencies; it does
not establish that no complete formalization exists elsewhere.

Source:
https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/a5154676af9aa3095150ee410cdda80555aa0642/PrimeNumberTheoremAnd/IEANTN/RosserSchoenfeld/RosserSchoenfeldZeta.lean

## Execution boundary

The user's current acceptance limit is 300 seconds per theorem on Prove2Me.
The previously checked million-prefix certificate took 1864.6460892 seconds
locally and is not platform-ready. Finite certificate expansion is suspended
in favor of this infinite-range obligation. No new Lean runtime result is
claimed by this source audit. Previously proved error-to-Rosser algebraic
bridges remain reusable and need not be recreated.
