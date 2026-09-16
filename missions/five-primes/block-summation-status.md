# `theorem51_typeI_block_summation` — status

Target: `7b6bb2d9-e6fa-4629-80e7-f3a34b9ff416`
(`TaoFivePrimes.theorem51_typeI_block_summation`), **Open** on the platform.

This is the Type I half of Tao's §5.2: given a nonnegative `W` obeying the
pointwise envelope on the odd `d ≤ UV`, bound `Σ W` by Tao's `(5.17)` two-term
expression.  Delivery decision (user, 2026-09-15): *prove what closes; submit a
reduction if needed.*

## Two children (approved split)

| child | platform status | local file |
| --- | --- | --- |
| `TaoFivePrimes.theorem51_odd_vinogradov_min_sum` (Cor 3.5) | **Proved** | `examples/five-primes/Theorem51Cor35.lean` |
| `TaoFivePrimes.theorem51_typeI_block_assembly` | Open (in progress) | `examples/five-primes/Theorem51Assembly.lean` |

Child 1 is published inside the definition `TaoFivePrimes_BlockFoundationCor35`
(job `e0f3a3d9`).  Child 2 is published as the definition
`TaoFivePrimes_Theorem51Assembly` (job `06eaeee8` → **PUBLISHED**, theorem_id
`013f62c3-1d88-4f65-94e9-a43bc0280413`).

## What Child 2 currently contains

`examples/five-primes/Theorem51Assembly.lean`, §1-§10, all `sorry`-free:

* §1 coprimality transfer `q ⊥ a`, `q ∤ d` ⇒ `q ∤ ad`;
* §2 the small-`d` core of (5.16) at Tao's normalisation;
* §3 the **integral test** `Σ_{j≤J} x/(2jq+q/2) ≤ (x/2q)log(4J+1) + 2x/q`;
* §4 the **block family** `Ioc ((4jq+q)/2) ((4(j+1)q+q)/2)`, with coverage at
  index `⌊(2d−q−1)/(4q)⌋` (the naive `⌊(2d−q)/(4q)⌋` is false at `q=4, d=10`),
  uniqueness, disjointness, and telescoping;
* §5 the **envelope split** `env1 + env2`;
* §6 the small-`d` case, including the **double-angle transfer** of (5.16) from
  Tao's phase `π·4dα` to the node's `π·2α·d` — this is where the factor of two
  makes Tao's `2q`;
* §7 constant rounding: `4 log 2/π ≤ 0.89`, `4 ≤ (2/π)(8 − log 4)`,
  `block_constant_rounding`;
* §8 `log(4J+1) ≤ log(2UV/q+4)`;
* §9 `env1_freeze`, `sum_le_sum_biUnion`, `mem_blockIndexFinset_of`;
* §10 `min_add_const_le`, `block_envelope_le`, `block_sum_envelope_le` — the
  **per-block bound at the sharp block count 1**.

## The mechanism (settled by numeric probe, see `block-foundation/numeric/`)

With `A_d = (1/2)(x/d)log x + C`, `B_d = C/|sin(π·2α·d)|`,
`C = 4(log2)log 2x`, `X_j = (1/2)(x/L_j)log x`, `L_j = 2jq + q/2`:

1. `min (X_j + C) B_d ≤ min X_j B_d + C`, so a block costs
   `(Cor 3.5 at A = X_j) + (#odd d)·C`.
2. Cor 3.5 at `A = X_j` on a width-`2q` block gives `2X_j + (2/π)Cq log 4q`.
   The published count `⌊2q/(2q)⌋ + 1 = 2` over-counts: only `q` odd `d` lie in
   the block, i.e. a *single* reindexed (`m = (d−1)/2`) block, so the sharp
   count is **1** — that is Tao's `2A` slot with `A = X_j`, one `X_j` per block.
3. `#odd d ≤ q/2 + 1`, whose `C`-budget `(q/2+1)C ≤ qC + 2C` is absorbed by
   Cor 3.5's `+4q` slack.

Numeric confirmation: `max(envelope / platform-RHS) = 0.44` over the admissible
region; Tao's per-block RHS has **0** violations over 12501/5001/501 blocks at
`q = 4/10/100`.

> **Correction of an earlier wrong conclusion.**  An earlier pass reported that
> the node was over-strong by a factor growing like `q`.  That came from
> evaluating the envelope at `x` far above `4·UV`; see
> `block-foundation/numeric/README.md` for the trap and the correct sweep.

## Remaining gap (the only genuinely new obligation)

**Sharpened Corollary 3.5**: on a range of width exactly `2q`, the count is `1`
rather than the published `2`.  §10 names this as the hypothesis `hblock`.
The reindexing half is already proved (`odd_min_sum_reindex` in
`Theorem51Cor35.lean`); §13 of that file adds the count bookkeeping
(`block_count_width_two_q`, `sharp_block_count`).  The analytic content is
Tao's Lemma 3.4 / his `(3.7)` block argument.

Once that is in hand, the summit is glue: §6 (small `d`) + §10 (per block) +
§3 (integral test) + §7/§8 (rounding) + §4 (coverage/disjointness) combined with
`sum_le_sum_biUnion`.

## Next actions

1. Finish the sharpened Cor 3.5 (or expose it as a third child if the platform
   budget allows).
2. Assemble the summit; audit `sorry`-freeness.
3. Submit the parent `theorem51_typeI_block_summation` as a **SKETCH
   reduction** importing Child 1 and Child 2.
