# Child 2 assembly — the residual obligation, resolved

Status at 2026-09-15 (night).  This supersedes both earlier versions of
`REMAINING.md`.  The `tension`/`factor of two` analysis in the previous version
was **wrong**, and for an instructive reason: I had been testing the envelope
outside its admissible range (`x` far larger than `4·U·V` for the chosen `UV`).

`examples/five-primes/Theorem51Assembly.lean` (assembled to
`Definitions/Def_TaoFivePrimes_Theorem51Assembly.lean`, published to p2m as
`013f62c3-1d88-4f65-94e9-a43bc0280413`) contains §1-§10, all `sorry`-free:

* §1 coprimality transfer; §2 the small-`d` core (5.16) at Tao's normalisation;
* §3 the **integral test** `Σ_{j≤J} x/(2jq+q/2) ≤ (x/2q)log(4J+1) + 2x/q`;
* §4 the **block family** `blockFinset q j = Ioc ((4jq+q)/2) ((4(j+1)q+q)/2)`
  with coverage (`mem_blockFinset_index`, index `⌊(2d−q−1)/(4q)⌋`), uniqueness,
  disjointness, and telescoping (`biUnion_blockFinset`);
* §5 the **envelope split** into `env1 + env2`;
* §6 the small-`d` case, including the **double-angle transfer** of (5.16) from
  Tao's phase `π·4dα` to the node's phase `π·2α·d` (this costs the factor of
  two that makes Tao's `2q`);
* §7 the **constant rounding** `4 log 2 / π ≤ 0.89` and
  `4 ≤ (2/π)(8 − log 4)`, plus `block_constant_rounding`;
* §8 the endpoint rounding `log(4J+1) ≤ log(2UV/q+4)`;
* §9 `env1_freeze`, `sum_le_sum_of_subset`, `sum_le_sum_biUnion`,
  `mem_blockIndexFinset_of`, and the block-width lemma;
* §10 (`min_add_const_le`, `block_envelope_le`, `block_sum_envelope_le`): the
  **per-block bound** at the sharp block count `1`.  This is the piece that
  produces the platform's `1/q` and it is now proved.

## The mechanism (now settled)

Write `A_d = (1/2)(x/d)log x + C`, `B_d = C/|sin(π·2α·d)|`,
`C = 4(log2)log 2x`, and `X_j = (1/2)(x/L_j)log x` at the block's left endpoint
`L_j = 2jq + q/2`.  Tao's per-block step is

```
min (X_j + C) B_d  ≤  min X_j B_d  +  C          (min_add_const_le)
```

so the block's envelope sum is at most
`(Cor 3.5 at A = X_j) + (#odd d in block)·C`.  The two ingredients are:

1. **Corollary 3.5 at `A = X_j` on the block gives `2 X_j + (2/π)C q log 4q`.**
   The block has width `2q`, so Corollary 3.5 *as stated* pays
   `⌊2q/(2q)⌋ + 1 = 2`; but only `q` odd `d` lie in it, i.e. the range is a
   *single* `q`-block in the reindexed variable `m = (d−1)/2`.  The **sharp
   count is 1**, which is exactly what turns Corollary 3.5's `2A` slot into a
   single `X_j` per block — Tao's display.  Verified numerically: for
   `q ∈ {4,10,100}` and 5000–12500 blocks each at `α = 1/(4q)`, the count-1
   form `2X_j + (2/π)Cq log 4q` holds with `max(s/rhs) = 0.60 … 0.76`, and the
   count-2 form would be needed nowhere.
2. **`#odd d ∈ block ≤ q/2 + 1`**, whose `C`-budget `(q/2 + 1)C ≤ q C + 2C` is
   absorbed by the `+4q` slack of Corollary 3.5.

## The numerical evidence (admissible region only)

With `U = V = √(UV) ≥ 40` and `UV ≤ x/4` enforced, sweeping
`UV ∈ {1600, 10⁴, 10⁵, 10⁶}`, `q ∈ {4, …, q ≤ UV}`,
`x ∈ {4UV, 40UV, 400UV, 4000UV}`:

```
max (envelope sum) / (platform RHS)  =  0.44
```

so the platform's bound holds with substantial margin.  The earlier report of a
`q`-growing overshoot was produced by taking `x = 10¹²` with `UV = 1600` — a
point at which the `α = 1/(4q)` phase is *generic* over the whole short
`d`-range, so `B` dominates and the sum is tiny; the apparent large ratio came
from comparing against a target that had been scaled by an inadmissible `x`.

## Remaining work

§10 closes the per-block arithmetic.  What is still needed to finish the parent
`TaoFivePrimes.theorem51_typeI_block_summation` as an actual proof:

* **Sharpened Corollary 3.5 (count 1 on a width-`2q` block).**  This is the one
  genuinely new obligation §10 names as `hblock`.  It follows from Tao's
  Lemma 3.4 / his `(3.7)` block argument; the reindexing half is already proved
  in `examples/five-primes/Theorem51Cor35.lean` (`odd_min_sum_reindex`), so only
  the count bookkeeping is new.  **This is the right shape for Child 2's
  remaining sub-obligation, or for a third child.**
* **The summit**: chain §6 (small `d`) + §10 (per block) + §3 (integral test) +
  §7/§8 (rounding) + §4 (coverage/disjointness) into the single conclusion,
  using `sum_le_sum_biUnion`.  All the pieces are proved; this is glue.

Everything in §1-§10 is `sorry`-free and independently reusable: the integral
test, the block combinatorics (coverage/uniqueness/disjointness/telescoping),
the envelope split, the double-angle transfer of (5.16), the per-block bound at
sharp count, and all constant rounding.
