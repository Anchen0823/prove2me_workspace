# Reduction of `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid`

## Target

For every real `t` with `1420 ≤ t ≤ 10 ^ 10`,

```lean
t * (1 - 1 / (2 * Real.log t)) < Chebyshev.theta t
```

Rosser–Schoenfeld (1962), *Approximate formulas for some functions of prime
numbers*, Illinois J. Math. **6**, Theorem 4, eq. (3.14), in the middle range
`1420 ≤ t ≤ 10^10`.

## Why this reduction is worth having

The target node already carries a decomposition, but it is a stub: it reduces
`..._analytic_mid` to its own parent `..._analytic` (submission `c15cf4b1`), so
it does not expose any obligation. Meanwhile the sibling node
`..._analytic_large` covers `t ≥ 10^10` and is now itself reduced to
`TaoFivePrimes.schoenfeld_psi_error_large`. So the range `1420 ≤ t ≤ 10^10` is
the last piece of the `θ` chain that is not wired to anything.

This submission wires it to exactly two inputs, one of which is the already
published analytic node.

## The reduction

Split the range at `10 ^ 9`.

**Case `1420 ≤ t ≤ 10^9`.** This is the new platform child
`TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid_lower`
(`fa58620e-0727-4e9a-9ea0-8e7318b6aef5`), published as part of this submission.
It is the genuinely finite part: `10^9` is a seam, not a source constant, and it
was chosen as the largest round threshold for which the analytic argument below
still closes.

**Case `t ≥ 10^9`.** One analytic input:
`TaoFivePrimes.schoenfeld_psi_error_large`, i.e.
`|ψ(t) − t| ≤ t/(40 log t)` for `t ≥ 10^8`. Only the **lower** half
`ψ(t) ≥ t − t/(40 log t)` is used. With `L = log t > 0`:

1. Mathlib's `Chebyshev.psi_sub_theta_le` bounds the prime-power correction,
   `ψ(t) − θ(t) ≤ 2 √t · L`, so

   ```text
   θ(t) ≥ t − t/(40 L) − 2 √t L.
   ```

2. It remains to compare with `t − t/(2L)`, i.e. to prove

   ```text
   (19/40) √t > 2 L²      on  t ≥ 10^9.
   ```

## The numerical core

Write `u1 = √t`, `u2 = √u1`, `u3 = √u2`, `u4 = √u3`, so `u3 = t^(1/8)` and
`u4 = t^(1/16)`.

* `t = u4^16`, hence `log t = 16 log u4 ≤ 16 u4` by
  `Real.log_le_sub_one_of_pos`. So `(log t)² ≤ 256 u4² = 256 u3`.
* `√t = u1 = u3^4`.
* Therefore

  ```text
  2 L² ≤ 512 u3 < (19/40) u3^4 = (19/40) √t
  ```

  where the middle inequality is exactly `u3³ > 512/(19/40) = 1077.895…`.
* `t ≥ 10^9` gives `√t ≥ 31622` (since `31622² = 999 950 884 ≤ 10^9`),
  then `√√t ≥ 177` (since `177² = 31329 ≤ 31622`), then
  `u3 ≥ 13.3` (since `13.3² = 176.89 ≤ 177`). Hence
  `u3³ ≥ 13.3³ = 2352.637`, comfortably past `1077.895…`.

The chain `31622 → 177 → 13.3` is exactly the run of three `Real.le_sqrt_of_sq_le`
applications in the file.

## Scope — a reduction, not a proof

The target stays **Open**: `schoenfeld_psi_error_large` is Open, and so is the
new finite child. What the submission changes is the shape of the remaining
work:

* before: one finite obligation on `(1420, 10^10]`, with the analytic input
  `schoenfeld_psi_error_large` proving (3.14) only from `10^10` on;
* after: one finite obligation on `(1420, 10^9]` — ten times smaller, and
  squarely in the range where the mission's existing certificate machinery
  (`rosser_psi_certificate_*`, covering up to `10^8`) already operates — and the
  whole analytic part `[10^9, 10^10]` delegated to the published `ψ` node.

Note also that the sibling `..._analytic_large` is stated for `t ≥ 10^10` even
though its own reduction only needs `t ≳ 1.2·10^8`; the seam could be pushed
further down, but that is a change to a published node and is not attempted
here.

## Local verification

* `lake env lean Solutions/Sol_TaoFivePrimes_rosser_schoenfeld_theta_lower_analytic_mid.lean`
  — exit code 0, 55 s; the only diagnostic is the expected
  `unusedVariables` warning for `h2` (the target's `t ≤ 10^10` binder, which the
  case split replaces).
* No `sorry`, no `axiom`, no `unsafe` in the body. Non-Mathlib imports: the two
  platform nodes named above.
* sha256 `2189a7eca7f3f1ef6b7b60b2209652f422ddf6261a15968217052cbf35e0494c`
  (154 lines).
