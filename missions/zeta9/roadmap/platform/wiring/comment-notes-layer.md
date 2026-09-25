## Notes-layer batch, 25 September 2026 — four more note-proved nodes are on the platform

Following the DAG wiring of this morning, the next four definition-free items from the
local mathematical notebook are now published, proved and linked to milestones. All
four were read back blind by an independent auditor before publication.

| new theorem | status | milestone | child edge |
|---|---|---|---|
| `ZetaNine.five_sample_sign_forces_nonzero` | Proved | TP3 | ← `quadrature_exact_of_moments` |
| `ZetaNine.min_lt_weighted_average_lt_max` | Proved | FI1 | — |
| `ZetaNine.mediant_strictly_between_min_and_max` | Proved | FI2 | ← `min_lt_weighted_average_lt_max` |
| `ZetaNine.positive_matrix_maps_nonneg_to_pos` | Proved | TA1 | — |

What each one actually formalises, and what it does not:

* **TP3** is the non-vanishing certificate: for a real functional `L`, five distinct
  nodes, strictly positive weights and moment agreement on degrees zero through four,
  any nonzero quartic whose five sampled values are weakly of one sign has `L p ≠ 0`.
  The reason is a root count — a nonzero quartic cannot vanish at five distinct nodes —
  so this is exactly FQ's cubature identity composed with TP's non-vanishing claim. It
  does **not** assert that the construction's weights are positive (that is the
  Gaussian-moment input GC) and it does **not** assert that any actual moving output
  passes the test (open target T5).
* **FI1** is the ordering step: positive weights summing to one put the weighted
  average strictly between a sampled value below and one above, whenever the sampled
  vector is not constant. Non-constancy is load-bearing and is the abstract counterpart
  of the rank-two non-degeneracy of the inverse image.
* **FI2** is the same content in invariant form, with no normalisation assumed and
  strict positivity of the denominators as an explicit hypothesis; the proof reweights
  by `v_j = w_j b_j / Σ_i w_i b_i`, so it is a genuine reduction onto FI1.
* **TA1** isolates the cone step of TA — a strictly positive matrix sends a nonzero
  nonnegative vector into the strictly positive cone — which is the step that works at
  two steps but fails at one, matching the note's observation that `H_n H_{n+2}` is
  eventually positive while the one-step transfer has mixed signs.

None of the four asserts weight positivity, eventual positivity of the actual transfer,
or any infinite sign/shortness condition on the concrete moving outputs. The concrete
definition layer is still absent, so the arithmetic arrows `V ← VA,Q,X`, `VA ← VB,Y`,
`VB ← VC,H,Z` remain unposted for the two structural reasons recorded in the mission
description. Mission milestones: 40 → 44, of which 15 are linked to theorem items.

Local record: `roadmap/platform/wiring/README.md`, receipts
`wiring/notes-layer-receipt.json`, blind report
`wiring/readback-notes-layer-2026-09-25.md`.
