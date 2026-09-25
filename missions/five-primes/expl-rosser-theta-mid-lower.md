# Reduction of `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid_lower`

## Target

For every real `t` with `1420 ≤ t ≤ 10 ^ 9`,

```lean
t * (1 - 1 / (2 * Real.log t)) < Chebyshev.theta t
```

the `1420 ≤ t ≤ 10^9` stage of Rosser–Schoenfeld (1962), Theorem 4, eq. (3.14).
This node was published earlier today as a child of
`..._theta_lower_analytic_mid`; this submission decomposes it in turn, so that
the whole `θ` chain ends in exactly one finite range and one analytic node.

## The split, and why `10^8` is the floor

`10^8` is the **hypothesis threshold of the analytic input**
`TaoFivePrimes.schoenfeld_psi_error_large` (`|ψ(t) − t| ≤ t/(40 log t)`,
`t ≥ 10^8`). It cannot be lowered without replacing that node, so `(1420, 10^8]`
is the smallest range the analytic method cannot reach, and it is the natural
place to stop splitting.

* `1420 ≤ t ≤ 10^8`: the new platform child
  `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_finite`
  (`7c1e7cb4-907c-4ef7-8622-bc5873ed4f44`), published as part of this
  submission. This is the finite obligation.
* `10^8 ≤ t ≤ 10^9`: `schoenfeld_psi_error_large` together with Mathlib's
  `Chebyshev.psi_sub_theta_le`, `ψ(t) − θ(t) ≤ 2√t·log t`. Only the **lower**
  half `ψ(t) ≥ t − t/(40 log t)` is used.

In the second case, writing `L = log t`, the two inputs give
`θ(t) ≥ t − t/(40L) − 2√t·L`, so the target follows from

```text
2 L² < (19/40) √t      on  10^8 ≤ t ≤ 10^9.
```

## The numerical core, in two regimes

**Regime 1, `10^8 ≤ t ≤ 2^27`.** Write `z = t/2^26 ≤ 2`. Then
`t = 2^26 · z`, so by `Real.log_mul` and `Real.log_pow`

```text
log t = 26 log 2 + log z ≤ 26 log 2 + z − 1 < 18.022 + 2 − 1 < 19.03,
```

the first inequality being `Real.log_le_sub_one_of_pos` and
`log 2 < 0.6931471808` the Mathlib bound `Real.log_two_lt_d9`. Since `t ≥ 10^8`
gives `√t ≥ 10^4`,

```text
2 L² ≤ 2 · 19.03² = 724.3 < 4750 = (19/40) · 10^4 ≤ (19/40) √t.
```

The trick here is that subtracting `1` — that is, using
`log z ≤ z − 1` rather than `log z ≤ z` — is what makes the constant small
enough; the alternative `log t ≤ 16 t^(1/16)` used below needs `t ≳ 1.22·10^8`
and so does not reach `t = 10^8`.

**Regime 2, `t ≥ 2^27`.** Four nested square roots: with
`u4 = t^(1/16)`, `u3 = t^(1/8)`,

```text
t = u4^16,  log t = 16 log u4 ≤ 16 u4  ⟹  L² ≤ 256 u4² = 256 u3,
√t = u3^4,
```

so `2L² ≤ 512 u3 < (19/40) u3^4 = (19/40)√t` as soon as
`u3³ > 512/(19/40) = 1077.895`. From `t ≥ 2^27` we get `√t ≥ 11585`
(`11585² = 134 212 225 ≤ 2^27`), then `√√t ≥ 107.6` (`107.6² = 11577.76 ≤ 11585`),
then `u3 ≥ 10.37` (`10.37² = 107.5369 ≤ 107.6`), and
`10.37³ = 1115.15 > 1077.895`. Each step is a `Real.le_sqrt_of_sq_le`
application in the file.

## Scope — a reduction, not a proof

The target stays Open. What changes is that the residual finite obligation is now
`(1420, 10^8]`, the smallest range the method can leave behind, and the range
`[10^8, 10^9]` is discharged by the published `ψ` node. The sibling node
`..._theta_lower_analytic_large` (`t ≥ 10^10`) was likewise reduced to
`schoenfeld_psi_error_large` earlier today, so the `θ` chain now reads

```text
theta_lower_finite [255,1420]  (Proved)
theta_lower_analytic_finite (1420, 10^8]  (Open, the finite task)
schoenfeld_psi_error_large                (Open, the analytic task)
```

Concretely this mirrors the already-Proved `rosser_schoenfeld_psi_bound`
decomposition, which is `{rosser_psi_finite_middle (1000, 10^8), psi_error_large}`:
the same shape, and the same `10^8` seam.

Note for whoever attempts the finite node: it is a *lower* bound on `θ`, so the
method that certifies `ψ` here — exhibiting `k` with `Nat.lcmUpto n ≤ 2^k` and
letting the kernel check it — does not transfer directly, since `θ` is the
logarithm of a primorial rather than of an lcm and there is no small integer to
exhibit. That is a genuine gap, recorded here rather than papered over.

## Local verification

* `lake env lean Solutions/Sol_TaoFivePrimes_rosser_schoenfeld_theta_lower_analytic_mid_lower.lean`
  — exit 0, 53 s; only the expected `unusedVariables` warning for `h2` (the
  target's `t ≤ 10^9` binder, which the case split replaces).
* No `sorry`, no `axiom`, no `unsafe` in the body. Non-Mathlib imports: the two
  platform nodes named above.
* sha256 `1642e035a8beda4ba5a34840dd745dbe7f0b7a8d5b892799e0ca656bcd911fc7`
  (185 lines).
