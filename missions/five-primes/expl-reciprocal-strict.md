# Reduction of `TaoFivePrimes.reciprocal_prime_sum_upper_bound_strict`

## Target

For every real `x ≥ 10⁸`,

```text
Σ_{p ≤ x} 1/p  <  log log x + γ + Σ'_p (log (1 − 1/p) + 1/p) + log (1 + 1/(2 log²x)).
```

Writing `B := γ + Σ'_p (log (1 − 1/p) + 1/p)` for the Meissel–Mertens constant — the
form the platform nodes use — and `A₁(x) := Σ_{p≤x} 1/p − log log x − B`, the target
is exactly

```text
A₁(x)  <  log (1 + 1/(2 log²x)).
```

## The single input

Mawia's explicit Mertens sum (`TaoFivePrimes.mawia_reciprocal_sum_bound`, published
today as `a182289a-f875-49fa-b946-9402fe0a3503`; R. Mawia, *Explicit Mertens sums*,
2017, zbMATH Zbl 1412.11125, tabulated in the TME-EMT wiki):

```text
|A₁(x)|  ≤  4 / log³x         (x ≥ 2).
```

This is far stronger than what is needed. Everything else in the file is elementary:

* `log (10⁸) > 16`, from `Real.exp 2 < 10` (which follows from
  `Real.exp_one_lt_d9` and `Real.exp 2 = (exp 1)²`), then `Real.log_pow`;
* hence `u := log x ≥ 16` by monotonicity of `log`;
* `log (1 + z) ≥ z/(1 + z)`, obtained from `Real.log_le_sub_one_of_pos` applied to
  `(1+z)⁻¹` and `Real.log_inv` — this gives
  `log (1 + 1/(2u²)) ≥ 1/(2u² + 1)`;
* `4/u³ < 1/(2u² + 1)` because `4(2u² + 1) < u³` for `u ≥ 16` (`nlinarith`);
* so `4/log³x < log (1 + 1/(2 log²x))`, and combining with the Mawia bound,
  `A₁(x) ≤ 4/log³x < log (1 + 1/(2 log²x))` — **strict**, as the node requires.

## Why not the Chebyshev route

The natural-looking route is Abel summation of the published Chebyshev input
`|ψ(t) − t| ≤ t/(40 log t)` (`TaoFivePrimes.schoenfeld_psi_error_large`). It cannot
work, and this is worth recording because it looks like it should. R–S p. 74 give the
identity (reproduced verbatim as (6.1)–(6.2) in Axler, arXiv:2203.05917, §6):

```text
A₁(x) = (ϑ(x) − x)/(x log x) − ∫_x^∞ (ϑ(y) − y)(1 + log y)/(y² log² y) dy.
```

Feeding in `|ϑ(y) − y| ≤ c·y/log^k y` produces `|A₁(x)| ≤ c(1/(k log^k x) + 1/((k+1) log^{k+1} x))`,
so a **one-log** input gives an error `≈ c/log x` — larger than the `1/(2 log²x)`
allowance for every `x ≳ 1.0668·10⁸` (at `x = 10⁸` the route's bound is `1.4677·10⁻³`
against an allowance of `1.4724·10⁻³`: it fits by 0.3 % and fails immediately after).
By contrast a two-log input suffices with `c ≤ 0.49`, which is essentially the content
of Mawia's theorem here (`4/log³x` is a three-log bound). Full audit, tables and
reproduction scripts: `missions/five-primes/A-star-route-audit.md`.

## Scope

A reduction, not a proof: the target stays Open and the residual obligation is the
single quoted external result `TaoFivePrimes.mawia_reciprocal_sum_bound`. What this
buys is that the reciprocal-prime bound now rests on a *published, citable* explicit
estimate with a clean statement, instead of on a statement assembled by hand.

## Local verification

* `lake env lean Solutions/Sol_TaoFivePrimes_reciprocal_prime_sum_upper_bound_strict.lean`
  — exit 0, 1 m 49 s, no diagnostics.
* No `sorry`, `axiom`, `admit` or `unsafe` in this file. Sole non-Mathlib import:
  `Theorems.Thm_TaoFivePrimes_mawia_reciprocal_sum_bound` — the local `sorry`
  placeholder mirroring the published node, which is why the axiom closure here
  contains `sorryAx` and is not reported as a closed proof. The two `private`
  helper lemmas (`log_one_add_ge`, `log_ten_pow_eight_gt`) are fully proved.
* sha256 `247d61ff42c67d4151c9d29ec6be33b9c93e9c6cb29dc07b617377c5fa7186d2`
  (103 lines).
