# Reduction of `TaoFivePrimes.reciprocal_prime_sum_upper_bound`

This is the non-strict sibling of
`TaoFivePrimes.reciprocal_prime_sum_upper_bound_strict` (`d64844bc`), submitted at
the same time with the identical argument; see `expl-reciprocal-strict.md` for the
full write-up.

## Target

```text
Σ_{p ≤ x} 1/p  ≤  log log x + γ + Σ'_p (log (1 − 1/p) + 1/p) + log (1 + 1/(2 log²x))
```

for every real `x ≥ 10⁸`.

## Argument, in one paragraph

With `B := γ + Σ'_p (log (1 − 1/p) + 1/p)` and `A₁(x) := Σ_{p≤x} 1/p − log log x − B`,
Mawia's explicit Mertens sum (`TaoFivePrimes.mawia_reciprocal_sum_bound`,
`a182289a-f875-49fa-b946-9402fe0a3503`, R. Mawia *Explicit Mertens sums* 2017)
gives `|A₁(x)| ≤ 4/log³x` for `x ≥ 2`. Since `u := log x ≥ log (10⁸) > 16`, the
elementary bound `log (1 + z) ≥ z/(1+z)` gives
`log (1 + 1/(2u²)) ≥ 1/(2u²+1) > 4/u³`, hence
`A₁(x) ≤ 4/log³x < log (1 + 1/(2 log²x))`, which is the target. The file is
byte-identical to the strict one except that the conclusion is `≤`; the one-line
numeric part is proved in both (`log_one_add_ge` from `Real.log_le_sub_one_of_pos`
and `Real.log_inv`; `log (10⁸) > 16` from `Real.exp_one_lt_d9` and `Real.log_pow`).

## Local verification

* `lake env lean Solutions/Sol_TaoFivePrimes_reciprocal_prime_sum_upper_bound.lean`
  — exit 0, 1 m 39 s, no diagnostics; no `sorry`/`axiom`/`unsafe` in the file.
* Sole non-Mathlib import: `Theorems.Thm_TaoFivePrimes_mawia_reciprocal_sum_bound`
  (the local `sorry` placeholder for the published node).
* sha256 `fc6d449c2c1df92122cca37107bffffcd06399dd1cb46676494b21b35c055753` (103 lines).

## Scope

A reduction. The target stays Open; the residual obligation is the quoted external
result `TaoFivePrimes.mawia_reciprocal_sum_bound`. With its strict sibling, this
collapses the two hand-written reciprocal-prime bounds into one citation.
