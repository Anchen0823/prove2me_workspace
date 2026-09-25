# Reduction of `TaoFivePrimes.rosser_schoenfeld_product_log_bound_large`

## Target

For every real `x ≥ 10^8`,

```lean
∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log ((p : ℝ) / ((p : ℝ) - 1)) <
  Real.eulerMascheroniConstant + Real.log (Real.log x) + Real.log (1 + 1 / (2 * (Real.log x) ^ 2))
```

Rosser–Schoenfeld (1962), (3.29) in logarithmic form: the explicit Mertens product bound.

## The reduction

For every prime `p`,

```text
log (p/(p−1)) = 1/p − (log (1 − 1/p) + 1/p),
```

because `log(p/(p−1)) = log p − log(p−1)` while `log(1−1/p) = log(p−1) − log p`. Summing over
`Nat.primesLE ⌊x⌋₊` decomposes the target into the difference of two sums, and it is then enough to have

* **A_strict** — `TaoFivePrimes.reciprocal_prime_sum_upper_bound_strict`:
  `∑_{p≤x} 1/p < log log x + γ + T + δ(x)`, where `T := ∑'_p (log(1−1/p) + 1/p)`
  and `δ(x) := log(1 + 1/(2 log²x))`;
* **B** — `TaoFivePrimes.mertens_tail_le_partial_sum`:
  `T ≤ ∑_{p≤x} (log(1−1/p) + 1/p)`, i.e. the full series is dominated by every finite partial sum.

Subtracting, `T` cancels and the target follows. **The constant cancels exactly**, which is why both
nodes state Mertens' constant as `γ + ∑'_p(log(1−1/p) + 1/p)` rather than as a decimal: no numerical
value of `B₁` is needed anywhere, so the reduction does not hinge on the 10-digit value
`B₁ = 0.2614972128476…`.

The companion `TaoFivePrimes.reciprocal_prime_sum_upper_bound` (non-strict) is imported and used for
the intermediate `≤` statement, so it is a declared dependency rather than an unused node. Strictness
is genuinely needed: the target's conclusion is `<`, and `linarith` cannot turn a `≤` chain into it.

## Why this shape

`..._product_log_bound_large` was the **only** open input left to
`TaoFivePrimes.rosser_schoenfeld_product_bound` (`fce5d444`), whose sibling
`rosser_schoenfeld_product_log_bound_mid` (`700 ≤ x ≤ 10^8`) is already Proved, and it feeds the
totient branch of the mission. The reduction separates it into its two classical halves:

| half | node | character |
| --- | --- | --- |
| analytic | `reciprocal_prime_sum_upper_bound(_strict)` | R–S Lemma 13 (8.9); follow from `schoenfeld_psi_error_large` by partial summation |
| elementary | `mertens_tail_le_partial_sum` | convergence of a series of negative terms; no prime-counting input |

## Scope — a reduction, not a proof

The target stays Open; all three children stay Open. What the submission establishes is that the
remaining content is **exactly** those two statements — in particular it removes the need to ever pin
down Mertens' constant numerically, which is the step that would otherwise make the node hard to state
let alone prove.

## Local verification

* `lake env lean Solutions/Sol_TaoFivePrimes_rosser_schoenfeld_product_log_bound_large.lean`
  — exit 0, 87 s, no diagnostics.
* No `sorry`, no `axiom`, no `unsafe`. Non-Mathlib imports: the three platform nodes named above.
