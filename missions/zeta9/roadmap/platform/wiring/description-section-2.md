
### Notes-layer batch, 25 September 2026

Four further definition-free items are now `Proved` on the platform, and two of them
add edges to the dependency graph:

| item | children |
|---|---|
| `ZetaNine.five_sample_sign_forces_nonzero` | `ZetaNine.quadrature_exact_of_moments` |
| `ZetaNine.min_lt_weighted_average_lt_max` | — |
| `ZetaNine.mediant_strictly_between_min_and_max` | `ZetaNine.min_lt_weighted_average_lt_max` |
| `ZetaNine.positive_matrix_maps_nonneg_to_pos` | — |

`five_sample_sign_forces_nonzero` is the formalised **non-vanishing certificate**: for
a real functional $L$, five distinct nodes $y$, strictly positive weights $w$ and
moment agreement on degrees zero through four, every nonzero quartic whose five sampled
values are weakly of one sign satisfies $L(p)\\ne0$. The root count excludes a quartic
vanishing at all five nodes, so this is exactly the composition of FQ's cubature
identity with TP's non-vanishing claim, and it is why the five-sample test needs no
sign check between the sampled points.

`min_lt_weighted_average_lt_max` is the ordering step of node FI: positive weights
summing to one put the weighted average strictly between a sampled value below and one
above, provided the sampled vector is not constant — the abstract counterpart of the
rank-two non-degeneracy of the inverse image. `mediant_strictly_between_min_and_max` is
the same statement in invariant form, with no normalisation assumed and strict
positivity of the denominators as a hypothesis; it is proved by reweighting with
$v_j=w_jb_j/\\sum_iw_ib_i$ and is therefore a genuine reduction onto the sandwich lemma
rather than a restatement. `positive_matrix_maps_nonneg_to_pos` isolates the cone step
of node TA, which the note needs because the one-step Taylor transfer has mixed signs
while the two-step transfer is eventually strictly positive.

All four statements were read back blind and independently before publication. As with
the previous batches, none of them asserts positivity of the actual cubature weights,
the eventual positivity of the actual transfer matrix, or any infinite sign or
shortness condition on the concrete moving outputs, and the concrete definition layer
described below is still absent, so the arithmetic arrows remain unposted.
