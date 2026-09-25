# ζ(9) DAG wiring — 2026-09-25

This directory records the work that put the mission's formalisable layer onto the
platform. Everything here is reproducible from the workspace root; the platform
state is captured in [wiring-receipt.json](wiring-receipt.json).

## What was done

Before this session the mission had four proposal items and three linked theorems:
the Zudilin reference, the two-form criterion, the volume/shape margin bridge, and
the three abstract arithmetic cores Q2/Y1/YD. The goal theorem
`ZetaNine.irrational_zeta_nine` had **no children at all** in the platform
dependency graph — the mission's milestone list described arrows that the theorem
graph did not contain.

Now:

| node | status | milestone |
|---|---|---|
| `ZetaNine.irrational_of_small_nonzero_integer_forms` | Proved | TP2 |
| `ZetaNine.taylor_sign_implies_kernel_sum_pos` | Proved | TP1 |
| `ZetaNine.quadrature_exact_of_moments` | Proved | FQ1 |
| `ZetaNine.exponentially_small_nonzero_forms_of_zeta_nine` | Open | R1 |
| `ZetaNine.exponentially_small_independent_forms_of_zeta_nine` | Open | R2 |

and the goal carries two accepted decompositions:

| route | children | verdict |
|---|---|---|
| one-form | `…irrational_of_small_nonzero_integer_forms` + `…exponentially_small_nonzero_forms_of_zeta_nine` | SKETCH_ACCEPTED |
| two-form | `…irrational_of_two_small_integer_forms` + `…exponentially_small_independent_forms_of_zeta_nine` | SKETCH_ACCEPTED |

The goal stays **Open**, as it must: each route's open child is strictly stronger
than the goal and is not equivalent to it.

## Files

- `OneFormCriterion.lean`, `PositiveKernelSign.lean`, `QuadratureMoments.lean`,
  `ExponentialOneFormObligation.lean`, `ExponentialTwoFormObligation.lean` — the five
  draft statements, in the platform's `namespace ZetaNine … end ZetaNine` layout.
- `*-statement.md` — the natural-language statements published with them.
- `solutions/Sol_*.lean` — the five submissions (three direct proofs, two reductions
  of the goal). All compile locally with `lake env lean`.
- `solutions/*-explanation.md` — the explanations published with each submission,
  including the explicit scope limits.
- `blind-readback-input.lean` + `readback-2026-09-25.md` — the blind audit input and
  the auditor's report (all five verdicts faithful and well-posed, with the one
  flagged asymmetry resolved and documented).
- `publish_wiring.py` — publish / poll-jobs / prove / reduce / poll-proofs /
  sync-mission / dump.
- `update_description.py` — appends the mission-description section and refreshes
  the description hash in `../new-results-receipt.json`.
- `state-before.json` — milestone snapshot taken before any write.
- `comment.md` — the mission discussion comment (id `7463b390`).

## Reproduce

```bash
py=.../python.exe
"$py" missions/zeta9/roadmap/platform/wiring/publish_wiring.py --dump
"$py" missions/zeta9/roadmap/platform/wiring/publish_wiring.py --publish
"$py" missions/zeta9/roadmap/platform/wiring/publish_wiring.py --poll-jobs
"$py" missions/zeta9/roadmap/platform/wiring/publish_wiring.py --prove
"$py" missions/zeta9/roadmap/platform/wiring/publish_wiring.py --reduce
"$py" missions/zeta9/roadmap/platform/wiring/publish_wiring.py --poll-proofs
"$py" missions/zeta9/roadmap/platform/wiring/publish_wiring.py --sync-mission
```

Every write mode is idempotent (a recorded `job_id`/`submission_id` short-circuits)
and every mode read-back-verifies its result.

## Constraints discovered while doing this

1. **A child that is "small integer forms exist" is equivalent to the goal.** Once a
   criterion is available, the existence of arbitrarily small nonzero integer forms
   is the same statement as irrationality (Dirichlet gives it for every irrational;
   the criterion gives irrationality from it). Publishing it as the goal's child
   would be a disguised restatement, not a decomposition. The published children are
   therefore pinned to a **fixed exponential rate**, which no general irrational
   number is guaranteed to admit — that is what makes them strictly stronger.
2. **A reduction cannot use a parameterised parent.** A child theorem is a closed
   proposition; a parent that takes its hypotheses as free parameters cannot import
   it. So a genuine multi-level graph over the concrete nodes requires Lean
   definitions of the construction, with one closed statement item per node. This is
   why the arithmetic arrows (`V ← VA,Q,X`, `VA ← VB,Y`, `VB ← VC,H,Z`, …) are still
   not posted.
3. **The platform's version guard is worth honouring.** The API moved 0.10.9 →
   0.11.1 during the gap; `sync_private_proposal.py` refused to mint a token until
   the documentation delta was reviewed. The relevant 0.11 changes for this mission
   were the expanded faithfulness criteria, the new `Changes requested` proposal
   status, and the mission-level `POST /missions/:id/make-public` endpoint (not
   called).
4. `--poll-jobs` must persist the receipt; the first version printed the correct
   statuses without saving them, which made `--prove` see `PENDING`.

## Notes-layer batch (same day)

A second batch, driven by `publish_notes_layer.py` (receipt
[notes-layer-receipt.json](notes-layer-receipt.json)), put four more note-proved nodes
on the platform — milestone links 40 → 44 total, of which 15 are linked to theorem
items:

| node | status | milestone | child edge |
|---|---|---|---|
| `ZetaNine.five_sample_sign_forces_nonzero` | Proved | TP3 | ← `quadrature_exact_of_moments` |
| `ZetaNine.min_lt_weighted_average_lt_max` | Proved | FI1 | — |
| `ZetaNine.mediant_strictly_between_min_and_max` | Proved | FI2 | ← `min_lt_weighted_average_lt_max` |
| `ZetaNine.positive_matrix_maps_nonneg_to_pos` | Proved | TA1 | — |

Two of the four are genuine reductions, so the graph gained two more edges: the
five-sample non-vanishing certificate now hangs under the quadrature core, and the
invariant mediant under the sandwich lemma. Files: `FiveSampleNonvanishing.lean`,
`PositiveWeightSandwich.lean`, `RatioInterval.lean`, `PositiveCone.lean`, the matching
`*-statement.md`, the four `solutions/Sol_*.lean` (all four compile with
`lake env lean`) and the four `solutions/*-explanation.md`. Blind report:
[readback-notes-layer-2026-09-25.md](readback-notes-layer-2026-09-25.md).
Mission comment: `412f3b6b`.

### Two failure/learning notes from this batch

- **The mediant first came back `CE`.** Two causes, both recorded in
  `memory/LEAN-PITFALLS.md`: in this environment `rw` does not rewrite inside a `∑`
  binder (so `rw [div_eq_mul_inv, ← Finset.sum_mul]` silently changed only one of the
  two sides), and `set x := … with hx` already folds the target, so a following
  `rw [← hx]` fails with "pattern not found". Both were fixed by using
  `simp only [hv, div_eq_mul_inv, ← Finset.sum_mul, ← hB]`, which does traverse
  binders and honours `←` lemmas. The retry was accepted; `publish_notes_layer.py`
  now keeps a `history` of rejected attempts and retries instead of skipping.
- **Skipping the local compile is what cost the round.** The first mediant attempt was
  submitted while its local `lake env lean` run was still in flight; the platform
  caught the same errors the compiler would have. Compile first, then submit.

