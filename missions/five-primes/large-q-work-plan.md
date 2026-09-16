# Large-denominator unit-numerator envelope

The user explicitly requested this target after pausing the earlier mission run.
Scope this work to TaoFivePrimes.exp_sum_estimate_large_q_unit_source_envelope,
ID 3d23bf2a-4938-4e21-a27c-2733e36173b1, and submit its exact `solution`.

Fresh reads found the target Open, matching the pinned environment, with no
prior submissions, theorem dependencies, mentions, or audit flags. The exact
source was read in Tao arXiv:1201.6656v4, Theorem 5.1 (5.5)--(5.7) and the
Section 6 specialization for (1.12).

The local solution passes Lean with autoImplicit=false. It preserves all target
binders; three unused-hypothesis warnings are expected. The proof body has no
sorry. Verification hash: verification/large-q-local-result.json.

The reduction uses two genuinely Open inputs:

- New general modulus-two Theorem 5.1 alternative, without the later choices
  of U and V or a large-denominator restriction.
- Existing small_q_modulus_transfer_source_envelope, ID
  cba0b2b8-5272-44e3-8764-6f3c559ebc64, valid for positive q0.

The solution proves q0=0 separately (only n=1 can be coprime to zero and its
von Mangoldt value vanishes), checks the nonnegative RHS, and establishes the
three logarithm identities from U=x/V^2. It then uses the triangle inequality.
It does not claim to prove either analytic input.

Publication job 9bfbdc53-11a5-4feb-a954-dbe91cfe41c5 is queued for the new source.
Do not republish it. The guarded script scripts/submit_large_q_after_source.ps1
checks that job and the exact source/target/hash before making the one proof
submission. Follow the returned proof ID to a terminal verdict. No proof
submission has been sent at the time this note was created.

Local helper experiments are LargeQLogSpecialization.lean and
LargeQZeroModulus.lean; the final solution contains their checked versions.
No Git commit or push is authorized by this new theorem request alone.

## Source published; proof submitted

Source publication job 9bfbdc53-11a5-4feb-a954-dbe91cfe41c5 completed
successfully. The exact published statement and environment were checked;
see research/large-q-source-published.json. The analytic source remains Open.

Submitted the verified target file as
308e42ec-6604-4445-8b66-e021c99c18bb. Follow that same ID at GET /verify;
do not submit again. The latest verdict is stored in
verification/large-q-verdict.json. Submission response and attempt records
are verification/large-q-submit-response.json and large-q-submit-attempt.json.
The exact target binder and conclusion text was independently compared
with the solution header (whitespace-normalized) and matches.

## Terminal result: SKETCH_ACCEPTED

Submission 308e42ec-6604-4445-8b66-e021c99c18bb is SKETCH_ACCEPTED with
an empty error message (server updated_at 2026-09-12T21:27:47.290817+08:00).
A fresh target read confirms it remains Open. The accepted decomposition
contains exactly the two analytic theorem inputs described above, both Open:
- e1794571-24bf-41f1-8f08-9296fbea9a90, theorem51_unit_numerator_bound;
- cba0b2b8-5272-44e3-8764-6f3c559ebc64, small_q_modulus_transfer_source_envelope.

Evidence: verification/large-q-verdict.json,
research/large-q-after-sketch.json, and
research/large-q-decompositions-after-sketch.json.
The requested scoped contribution is complete. No publication or proof
verification job for this contribution remains pending. Do not start
another mission target without an explicit request. No commit or push was
performed for these new changes.
