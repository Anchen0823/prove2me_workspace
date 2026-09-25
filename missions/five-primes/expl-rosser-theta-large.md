# Reduction of `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_large`

## Target

For every real `t` with `t ≥ 10 ^ 10`,

```lean
t * (1 - 1 / (2 * Real.log t)) < Chebyshev.theta t
```

This is Rosser–Schoenfeld (1962), *Approximate formulas for some functions of
prime numbers*, Illinois J. Math. **6**, Theorem 10 / eq. (3.14), restricted to
the range past tabulated numerical verification. The mission's source field
records this as the large range of Tao arXiv:1201.6656v4.

## What is reduced to what

The reduction has exactly **one** analytic input, and it is already a published
node of this mission:

```lean
TaoFivePrimes.schoenfeld_psi_error_large (y : ℝ) (hy : 10 ^ 8 ≤ y) :
    |Chebyshev.psi y - y| ≤ y / (40 * Real.log y)
```

(Tao, arXiv:1201.6656v4, proof of Lemma 4.3, invoking Schoenfeld, *Sharper
bounds for the Chebyshev functions θ(x) and ψ(x). II*, Math. Comp. **30**
(1976), Theorem 7.)

**Only the lower half of that two-sided estimate is used**, namely
`psi t ≥ t − t/(40 log t)`. The "excess" half `psi t ≤ t + t/(40 log t)` plays
no role at all. Writing `L = log t > 0`:

1. Mathlib's `Chebyshev.psi_sub_theta_le` bounds the prime-power correction
   between the two Chebyshev functions: `psi t − theta t ≤ 2 * sqrt t * L`.
   Combining the two,

   ```text
   theta t ≥ psi t − 2 sqrt t L ≥ t − t/(40 L) − 2 sqrt t L.
   ```

2. The remaining comparison is `(19/40) * (t / L) > 2 * sqrt t * L`, which after
   multiplying by `L / sqrt t` is the elementary inequality

   ```text
   (19/40) * sqrt t > 2 * L^2.
   ```

   On `t ≥ 10^10` this is proved from the explicit logarithmic bound
   `log t ≤ 8 * t^(1/8)`, written here with three nested square roots (so it is
   a direct consequence of `Real.log_le_sub_one_of_pos`), together with
   `269.5 ≤ sqrt (sqrt t)`, which follows from `sqrt (10^5) ≥ 269.5`.
   Concretely, `L^2 ≤ 64 * sqrt (sqrt t)` and `2 * 64 = 128 < 269.5 * 19/40`.

So `theta t > t − t/(2L) = t * (1 − 1/(2L))`.

No numerical interval data, no Riemann hypothesis, and no multiplicative
explicit formula are used. The whole content is one explicit ψ-error bound plus
the elementary `θ ≤ ψ` correction.

## Scope — this is a reduction, not a proof

The target node remains **Open** until `schoenfeld_psi_error_large` is proved.
Concretely, the same arithmetic step already appears inside the accepted
reduction `ee89c952-2fee-4da1-af76-f935fe76ac11` of the parent node
`TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic` (which split
`t ≥ 1340` into the finite range, the middle range `1420 ≤ t ≤ 10^10`, and
`schoenfeld_psi_error_large`). The present submission records that step as a
standalone decomposition of the newly introduced `t ≥ 10^10` node, so that this
node is not left as a frontier leaf whose single missing input is a node that
already exists and is already Open in the tree.

Two honest caveats:

* Using the published `schoenfeld_psi_error_large` rather than the one-sided
  `schoenfeld_psi_deficit_lower_large` loses no generality in the reduced
  statement and keeps the dependency on the node that the mission's own
  decomposition of the parent already uses.
* Nothing here advances `schoenfeld_psi_error_large` itself; the explicit ψ
  error bound is the real analytic content and stays Open.

## Local verification

* `lake env lean Solutions/Sol_TaoFivePrimes_rosser_schoenfeld_theta_lower_analytic_large.lean`
  — exit code 0, no diagnostics, 63 s.
* The file body contains no `sorry`, no `axiom`, no `unsafe`. Its only
  non-Mathlib import is the single platform node named above.
* sha256 of the submitted file:
  `d6f19f0b3495d6502f56c3da7531b3b9759dd376265a777a3495171bd63b9b68`
  (119 lines).
