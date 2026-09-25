# Reduction of `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic`

## The target

\[
t\left(1-\frac{1}{2\log t}\right)<\theta(t) \qquad (t\ge 1340),
\]

Rosser--Schoenfeld (1962), Theorem 4, eq. (3.14). It is the input that Tao's
Section 9 uses to construct the parameter `y` of Lemma 15 in the range
`log n >= 1340`.

## The split

The submitted file proves the target from **one new child** plus **two already
published platform nodes**, splitting the range on `t`:

| range | used | status |
| --- | --- | --- |
| `1340 <= t <= 1420` | `TaoFivePrimes.rosser_schoenfeld_theta_lower_finite` | already **Proved** on the platform |
| `1420 <= t <= 10^10` | **new child** `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid` | proposed with this reduction |
| `10^10 <= t` | `TaoFivePrimes.schoenfeld_psi_error_large` | already published **Open** platform input |

### Range `1340 <= t <= 1420`

The proved finite node gives the *sharper* elementary bound
`t - 2 sqrt t < theta t`. It dominates (3.14) on this range because
`t * (1 - 1/(2 log t)) <= t - 2 sqrt t` is equivalent to `4 log t <= sqrt t`,
and that is proved here from

* `log t <= log 1420 <= log 2^11 = 11 log 2` (as `1420 <= 2048`) together with
  Mathlib's `Real.log_two_lt_d9`, giving `4 log t < 30.5`;
* `sqrt t >= sqrt 1340 > 36.6`, from `36.6^2 = 1339.56 <= 1340`.

So `4 log t < 30.5 < 36.6 < sqrt 1340 <= sqrt t`, and the same inequality
multiplied by `sqrt t > 0` is exactly `4 sqrt t log t <= t`, i.e.
`2 sqrt t <= t/(2 log t)`.

Nothing beyond the quoted finite node is assumed on this range.

### Range `10^10 <= t`

Two published/open inputs and one Mathlib lemma combine here:

* `TaoFivePrimes.schoenfeld_psi_error_large` is the explicit two-sided
  Chebyshev estimate `|psi t - t| <= t/(40 log t)` for `t >= 10^8`; its lower
  half gives `psi t >= t - t/(40 log t)`.
* Mathlib's `Chebyshev.psi_sub_theta_le` is the prime-power correction
  `psi t - theta t <= 2 sqrt t log t`. Together,
  `theta t >= t - t/(40 log t) - 2 sqrt t log t`.
* Hence it suffices that `t/(2 log t) - t/(40 log t) > 2 sqrt t log t`, i.e.
  `(19/40) sqrt t > 2 (log t)^2`, which is proved as follows: `log t <= 8 t^{1/8}`
  by `Real.log_le_sub_one_of_pos` applied to the eighth root (written in the
  file as three nested square roots, via `t = (t^{1/8})^8`), so
  `(log t)^2 <= 64 sqrt(sqrt t)`; and `sqrt(sqrt t) >= sqrt(sqrt (10^10)) >= 269.5`
  on this range, so `128 sqrt(sqrt t) <= (19/40) (sqrt(sqrt t))^2 = (19/40) sqrt t`.

The threshold `10^10` is chosen exactly so that the last comparison is
elementary: at `t = 10^10` we have `(19/40) sqrt(sqrt t) = 128.01... > 128`, and
the left-hand side grows.

### What is left

The child `rosser_schoenfeld_theta_lower_analytic_mid` isolates the remaining
obligation: the finite range `1420 <= t <= 10^10` of (3.14). Every other part
of the original unbounded statement is discharged here from nodes that are
already on the platform (one of them a finite computation that is already
proved, the other the explicit Schoenfeld input the mission already tracks).

## Hygiene

The submitted file contains no `sorry` and no `axiom`; its only imports are
`Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite`,
`Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_analytic_mid`,
`Theorems.Thm_TaoFivePrimes_schoenfeld_psi_error_large`, and Mathlib modules.
It compiles locally against the pinned toolchain `leanprover/lean4:v4.33.1`
and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` as a Lake module
(`lake build Solutions.Sol_TaoFivePrimes_rosser_schoenfeld_theta_lower_analytic`,
19 s), with the two mirrored platform statements supplied as local
placeholders exactly as the platform tracks them.

This is a reduction, not a proof of the child. Proving the child is a finite
verification over `1420 <= t <= 10^10`, of the same nature as the mission's
other numerical leaves; the reduction removes from it the two ranges that are
already settled.
