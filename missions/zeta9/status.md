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
