# Proof of `TaoFivePrimes.mertens_tail_le_partial_sum`

## Target

For every real `x`,

```lean
(∑' p : Nat.Primes, (Real.log (1 - 1 / p) + 1 / p)) ≤
  ∑ p ∈ Nat.primesLE ⌊x⌋₊, (Real.log (1 - 1 / p) + 1 / p)
```

This is a **complete proof**, not a reduction: the statement is closed here, and
no new obligation is introduced.

## What the statement says

`M := Σ_p (log (1 − 1/p) + 1/p)` is a convergent series of *negative* terms; its
value is Mertens' constant minus Euler's constant, `B₁ − γ ≈ −0.315718`. Since
every term is negative, finite partial sums decrease as terms are added, so every
finite partial sum *dominates* the total. That is exactly the claim — with the
partial sum taken over the primes `≤ ⌊x⌋`.

The lemma is the elementary half of the decomposition of
`TaoFivePrimes.rosser_schoenfeld_product_log_bound_large`: the analytic half
(Rosser–Schoenfeld (1962), Lemma 13, (8.9)) supplies the strict upper bound for
`Σ_{p ≤ x} 1/p`, and this lemma cancels the constant `B₁ − γ` against it. Both
sides of that comparison are written with `B₁` *as* `γ + Σ'_p (log (1 − 1/p) + 1/p)`,
so the two constants cancel symbolically and **no decimal approximation of
Mertens' constant is needed anywhere** — the remaining numerical content is
pushed into the sibling nodes `reciprocal_prime_sum_upper_bound` and
`reciprocal_prime_sum_upper_bound_strict`.

## Proof strategy

Three steps, all elementary; no prime number theorem, no zero-free region, no
explicit formula, no computation.

**1. `log (1 − 1/p) + 1/p ≤ 0`.** From `Real.log_le_sub_one_of_pos` applied to
`1 − 1/p > 0`: `log (1 − 1/p) ≤ (1 − 1/p) − 1 = −1/p`.

**2. `|log (1 − 1/p) + 1/p| ≤ 2/p²`.** Taking `x = 1/p` (`|x| < 1`) and `n = 1` in
Mathlib's `Real.abs_log_sub_add_sum_range_le`

```text
|Σ_{i<n} x^(i+1)/(i+1) + log (1 − x)| ≤ |x|^(n+1) / (1 − |x|)
```

gives `|1/p + log (1 − 1/p)| ≤ (1/p)²/(1 − 1/p) = 1/(p(p−1))`. Since `p ≥ 2`,
`p(p−1) ≥ p²/2`, so `1/(p(p−1)) ≤ 2/p²`. Combined with step 1,

```text
0 ≤ −(log (1 − 1/p) + 1/p) ≤ 2/p²   for every prime p.
```

**3. Summability and the comparison.** `Σ 2/n²` is summable over `ℕ`
(`Real.summable_one_div_nat_pow` with `p = 2`, times `2`), so by the comparison
test `Summable.of_nonneg_of_le` the sequence `n ↦ −(log (1 − 1/n) + 1/n)`,
extended by `0` off the primes, is summable; hence so is its negative
`mTailOnPrimes`.

The comparison itself is a one-line general lemma proved in the file: *if
`f : ι → ℝ` is summable and `f ≤ 0` pointwise, then `Σ'_i f i ≤ Σ_{i ∈ s} f i` for
every finite `s`*. It is `Summable.sum_le_tsum` applied to `−f ≥ 0`, then negated
(`Finset.sum_neg_distrib`, `tsum_neg`).

Finally the `tsum` over the subtype `Nat.Primes` is unfolded into a `tsum` over
`ℕ` by `tsum_subtype` (`Σ'_{x : s} f x = Σ'_x, s.indicator f x`), the indicator
is identified with the original summand on `Nat.primesLE ⌊x⌋₊` (every element of
that finset is prime, by `Nat.mem_primesLE`), and step 3 is applied.

## Local verification

* `lake env lean Solutions/Sol_TaoFivePrimes_mertens_tail_le_partial_sum.lean` —
  exit 0, 2 m 27 s, **no diagnostics at all**.
* `#print axioms solution` → `[propext, Classical.choice, Quot.sound]`, the three
  standard axioms only.
* No `sorry`, `axiom`, `admit` or `unsafe` in the file. Only Mathlib is imported;
  there is no dependency on any other platform node.
* sha256 `bad13442413d8a277dad7b74468b4e78ceafa9454cc4f81cf0e3c9b0cfd18c7e`
  (127 lines).

## Three formalisation notes worth recording

* The submitted file must define `solution` in the **root** namespace. An earlier
  version of this file wrapped everything in `namespace TaoFivePrimes … end`
  (copying the layout of the target's `formal_statement`); that submission was
  rejected with *"Your proof does not match the target type: Unknown identifier
  `solution`"*, because the declaration had become `TaoFivePrimes.solution`.
  The target's own `formal_statement` is written inside the namespace, but the
  submission is not.
* In this Mathlib, `Nat.Prime n` is *definitionally* `Irreducible n`, so when
  rewriting with `Set.indicator_of_mem`/`Set.indicator_of_notMem` against a goal
  containing `{m | Nat.Prime m}.indicator …`, the set argument has to be given
  explicitly as `(s := {m : ℕ | Nat.Prime m})`; otherwise the elaborator picks
  up `{m | Irreducible m}` from the hypothesis and the `rw` fails on a syntactic
  mismatch.
* `linarith` does not relate the literal forms `-1 / n` and `1 / n` to each
  other (it does not normalise `(-1)/n` to `-(1/n)` here). Stating the bound as
  `log (1 − 1/n) ≤ −(1 / n)` — with the negation outside the division — makes the
  subsequent `linarith` calls go through.
