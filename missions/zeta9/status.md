# Zeta(9) first research round

Completed 2026-09-24. Status: first research round complete; no irrationality
proof is claimed. See [the report](report.md) for results and proof boundaries.

Primary route: third-order integer poles, seventh-order endpoint zeros, and
sixth-derivative summation yielding a rational linear form in 1 and zeta(9).
Secondary route: positive simple-square-pole Gram determinants using the
general odd-zeta functional already implemented under missions/zeta7.

The 21 linear-form and 21 zeta9 Gram samples all have primitive absolute value
strictly above one. Two zeta5/zeta7 regression controls also passed. There were
no unresolved computation timeouts. No n448 candidate met the promotion gate.

Proved local results include the all-prime d_n^9/G integerization, the exact
large-prime gcd valuation and its asymptotic integral, and a global analytic
upper bound. The upper bound does not close to a negative exponent. Proofs
were cross-reviewed; no eventual nonvanishing or irrationality is established.

Exact coefficients, primitive normalization, hashes and Arb ball evidence are
stored under verification/. No Lean or external submission was performed.

## Proof-state audit (2026-09-25)

[An audit of the whole effort](research/zeta9-proof-state-audit.tex) ([Chinese
summary](research/zeta9-proof-state-audit-zh.md)) reconstructs the proof state
item by item, classifies every definition / lemma / numerical claim, draws the
dependency DAGs toward the irrationality of zeta(9), and lists every logical
gap. It repairs nothing. Part I covers the first research round; Part II covers
rounds 2-9, the local roadmap DAG (13 open nodes, 27 note-proved, none Lean
checked) and the private platform mission (open root, two SKETCH_ACCEPTED
decompositions, eight abstract theorem-level proofs).

Verdict: in Part I the analytic side supplies only *upper* bounds for the linear
form while the arithmetic side controls only denominators, so the route has no
mechanism for the decay a proof would need; in Part II every closing statement
is a for-all (over primitive directions, or over infinitely many n) while the
corpus holds five-scale finite certificates only, and the newest geometric lemma
(FQ) is vacuous below n ~ 1686 -- far beyond every parameter ever used. The
proved uniform arithmetic estimate stands at 22.337 against a requirement of
0.61071437.

The audit also re-verified, independently: the contour-identity orientation
sign; the H'/H'' phase data; the Gamma enclosures; the sup-H bounds; the
improved integerization t# = d_n^9/G on five parameters (including n=224); the
large-prime gcd formula on new data (216 parameters, 1951 prime terms, no
failures); the round5-7 saddle constants x_*, f(x_*), a (to full displayed
precision); the FQ sample-point activation threshold; and the true-kernel
five-point cubature weights. Scripts and transcripts:
verification/audit-2026-09-25/.

No irrationality statement is claimed at any point.

---

## 2026-09-25: platform DAG wiring

The private mission `8195d8fe-059f-4515-92b4-57b585e2bac6` now has the goal theorem
attached to real children. Before this session
`ZetaNine.irrational_zeta_nine` was a bare `Open` leaf with **zero** decompositions.
Now:

- five new private theorem items — three `Proved` general lemmas (the formalisable
  cores of nodes TP and FQ) and two `Open` obligations (R1, R2);
- two `SKETCH_ACCEPTED` decompositions of the goal, one per main line (one-form and
  two-form);
- five new milestone links (TP1, TP2, FQ1, R1, R2), 35 → 40 milestones;
- blind independent read-back for all five statements, all faithful;
- mission description and discussion updated (comment `7463b390`).

The goal remains **Open**. Neither open obligation is proved, and the concrete
construction still has no Lean definitions, so the arithmetic arrows
(`V ← VA,Q,X` etc.) are deliberately not posted yet. Full record:
`roadmap/platform/wiring/README.md`.

### Same day, notes-layer batch

Four more note-proved nodes were published, proved and milestone-linked
(`publish_notes_layer.py`, receipt `wiring/notes-layer-receipt.json`):

| node | milestone | child edge |
|---|---|---|
| `ZetaNine.five_sample_sign_forces_nonzero` | TP3 | ← `quadrature_exact_of_moments` |
| `ZetaNine.min_lt_weighted_average_lt_max` | FI1 | — |
| `ZetaNine.mediant_strictly_between_min_and_max` | FI2 | ← `min_lt_weighted_average_lt_max` |
| `ZetaNine.positive_matrix_maps_nonneg_to_pos` | TA1 | — |

Milestones 40 → 44, linked-to-theorem 11 → 15. Two new platform decomposition edges were
registered. The mediant first came back `CE` because of a local trap — in this
environment `rw` does not rewrite inside a `∑` binder, and `set … with hx` already
folds the target so `rw [← hx]` then fails; switching to `simp only [..., ← lemma]`
fixed it (recorded in `memory/LEAN-PITFALLS.md`). Blind read-back passed on all four.
Goal still **Open**.
