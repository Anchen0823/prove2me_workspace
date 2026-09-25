# Blind read-back, notes-layer batch (2026-09-25)

Input: `notes-layer-blind-input.lean` — the four new statements, with no doc comments,
no mission description, no research notes and no statement of intent. The auditor was
told to read only that file and `references/mission_auditor.md`, and to report what the
code literally says plus any vacuity, unsatisfiability or dead hypothesis.

The auditor's per-theorem verdicts, recorded verbatim in substance:

| theorem | verdict | substantive remarks |
|---|---|---|
| `ZetaNine.five_sample_sign_forces_nonzero` | `FAITHFUL AND WELL-POSED` | All hypotheses jointly satisfiable, none vacuous. Injectivity of `y`, positivity of `w` and the disjunctive sign hypothesis are each load-bearing; without the uniform sign `L p` could vanish. No division, so no hidden zero denominator. |
| `ZetaNine.min_lt_weighted_average_lt_max` | `FAITHFUL AND WELL-POSED` | Non-constancy is load-bearing: for constant `r` the average equals every value and both strict inequalities fail. `∑ w = 1` is what makes the undivided sum lie between the sampled values. |
| `ZetaNine.mediant_strictly_between_min_and_max` | `FAITHFUL AND WELL-POSED` | `hb` secures both the per-ratio denominators and the mediant denominator `∑ w·b`, which is a sum of strictly positive terms and hence provably nonzero — so the statement is well-posed, not merely the proof. Non-equality of the ratios is load-bearing. |
| `ZetaNine.positive_matrix_maps_nonneg_to_pos` | `FAITHFUL AND WELL-POSED` | `v ≠ 0` together with `v ≥ 0` forces some strictly positive component; each strict positivity of the entries is used. No division. |

No `SUSPECT` items, no dead hypothesis, no unsatisfiable hypothesis, and no statement
found false under its own hypotheses. The auditor was asked specifically to look for a
latent zero denominator in the mediant statement and confirmed that positivity of `b`
rules it out.

Method note: the read-back was produced by a separate sub-agent that had no access to
this mission, the campaign's research notes, or the author's intent. It is evidence
about what the statements *say*, not about whether they are the right statements for
the mathematics they are meant to formalise — that judgement is recorded separately in
the corresponding `*-statement.md` files under "Scope".
