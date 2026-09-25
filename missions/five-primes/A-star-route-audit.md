# Audit: what `reciprocal_prime_sum_upper_bound{,_strict}` actually needs

**Verdict up front.** The route recorded in `frontier-report-2026-09-24.md`
("A / A\*: Rosser–Schoenfeld (8.9), from `schoenfeld_psi_error_large` + Abel
summation") **does not work**. Abel summation of the pointwise hypothesis
`|ψ(t) − t| ≤ t/(40 log t)` produces an error term of size `1/(40 log x)`, which
exceeds the node's allowance `log(1 + 1/(2 log²x)) ≈ 1/(2 log²x)` for every
`x ≳ 1.067·10^8`. The route certifies only the sliver `10^8 ≤ x ≤ 1.067·10^8`
of the node's range — i.e. nothing. This correction is mine: the plan was my own
note, and it was wrong.

The fix is *not* "we need the Riemann hypothesis": the requirement is a Chebyshev
(`ϑ`) estimate with **at least two powers of `log`** in the denominator, and such
bounds are standard explicit results (a four-log one is tabulated in the
literature; see "What would actually work" below). What cannot work is the
platform's `1/log` node. The identity used below is not my invention — it is
R–S p. 74, reproduced verbatim as (6.1) in Axler, arXiv:2203.05917, §6.

## The two nodes

```lean
-- TaoFivePrimes.reciprocal_prime_sum_upper_bound_strict   (d64844bc, Open)
theorem ... (x : ℝ) (hx : 10 ^ 8 ≤ x) :
    (∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)) <
      Real.log (Real.log x) + Real.eulerMascheroniConstant +
        (∑' p : Nat.Primes, (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) +
        Real.log (1 + 1 / (2 * (Real.log x) ^ 2))
```

With `B₁ = γ + Σ'_p (log (1−1/p) + 1/p)` (Mertens' constant — the same constant
our node `mertens_tail_le_partial_sum` is built around), this reads

```text
Σ_{p ≤ x} 1/p  <  log log x + B₁ + log(1 + 1/(2 log²x)),
```

so the target is an explicit bound on the error
`err(x) := Σ_{p≤x} 1/p − log log x − B₁`, of size `≈ 1/(2 log²x)`.

## What the ψ hypothesis gives under Abel summation

Write `θ(t) = Σ_{p ≤ t} log p`, so `S(x) := Σ_{p≤x} 1/p = ∫_{2^-}^{x} dθ(t)/(t log t)`.
Abel summation, with `θ = t + E`:

```text
S(x) = 1/log x + ∫_2^x (log t + 1)/(t log²t) dt + [E-terms]
     = log log x + C₀ + E(x)/(x log x) + ∫_2^x E(t)(log t+1)/(t² log²t) dt ,
```

and since the constant `C₀` plus the same expression at `∞` is exactly `B₁`,

```text
err(x) = E(x)/(x log x) − ∫_x^∞ E(t)·(log t + 1)/(t² log² t) dt + O(x^{-1/2}),   (*)
```

the `O(x^{-1/2})` being the difference of the two prime-power corrections
(since `0 ≤ ψ − θ ≤ 2√t log t`).

Now insert the only hypothesis available, `|E(t)| ≤ t/(40 log t)` for `t ≥ 10^8`:

```text
E(x)/(x log x)                     ≤ 1/(40 log²x)
−∫_x^∞ E(...)dt ≤ ∫_x^∞ |E|(...)   ≤ (1/40)·(1/log x + 1/(2 log²x))
```

because `∫_x^∞ (log t+1)/(t log³t) dt = 1/log x + 1/(2 log²x)`. Hence

```text
err(x) ≤ 1/(40 log²x) + (1/40)(1/log x + 1/(2 log²x))  ,
```

whose **leading term is `1/(40 log x)`** — a factor `log x/20` larger than the
allowance `1/(2 log²x)`. Note that no cancellation is available: (*) contains
`−∫_x^∞ E`, and an upper bound on `E` is exactly what turns it into a positive
contribution.

Solving `1/(40 log²x) + (1/40)(1/log x + 1/(2 log²x)) = log(1 + 1/(2 log²x))`
gives `log x = 18.4854`, i.e.

```text
crossover  x = 1.0668·10^8 .
```

| `x` | target allowance | ψ-route bound | route / allowance |
|---|---|---|---|
| `1.0000·10^8` | `1.4724·10^-3` | `1.4677·10^-3` | **0.997** |
| `1.0668·10^8` | `1.4622·10^-3` | `1.4622·10^-3` | 1.000 |
| `1.7848·10^8` | `1.3841·10^-3` | `1.4197·10^-3` | 1.026 |
| `4.8517·10^8` | `1.2492·10^-3` | `1.3438·10^-3` | 1.076 |
| `1.0000·10^10` | `9.4261·10^-4` | `1.1565·10^-3` | 1.227 |

So even at the node's own threshold the route fits only with a `0.3 %` margin,
and it fails immediately afterwards.

## The statement is not false — the *bound* is too weak

A sieve to `10^8` (`tmp/check_reciprocal_prime_sum.py`, 5 761 455 primes,
`bytearray` + `math.fsum`) gives the true error `Σ_{p≤x} 1/p − log log x − B₁`:

| `x` | true error | allowance | margin |
|---|---|---|---|
| `10^6` | `3.8972·10^-5` | `2.6162·10^-3` | 67× |
| `10^7` | `9.5741·10^-6` | `1.9228·10^-3` | 201× |
| `10^8` | `4.0301·10^-6` | `1.4724·10^-3` | **365×** |

(The error drops by a factor `≈ 0.1` per factor `100` in `x`, which is the
`≍ x^{-1/2}` behaviour predicted by RH; the platform's hypothesis at `x = 10^8`
allows `1/(40 log x) = 1.357·10^-3`, i.e. 337× more than the actual error. The
ψ-route bound `1.468·10^-3` is therefore ~364× larger than the quantity it is
trying to bound.)

So `reciprocal_prime_sum_upper_bound{,_strict}` is a *true and well-supported*
statement; the problem is purely that a pointwise Chebyshev bound of the form
`t/(40 log t)` loses everything when integrated against `dt/(t log² t)`.

## A shortcut that does not exist

Because (6.1) reads `A₁(x) = f(x)/(x log x) − ∫_x^∞ f(y)w(y) dy` with
`f = ϑ − id`, it is tempting to argue: *if `f(y) ≥ 0` in the tail then the
integral is negative and `A₁(x) ≤ f(x)/(x log x) ≤ 1/(40 log²x)` would follow from
the ψ node alone.* That would have made the reduction cheap. **It is false on the
reachable range**: `tmp/check_theta_sign.py` (sieve to `10^8`) gives

| `x` | `ϑ(x) − x` | `(ϑ(x) − x)/√x` |
|---|---|---|
| `10^6` | `−1515.8` | `−1.516` |
| `10^7` | `−4820.7` | `−1.524` |
| `10^8` | `−12269.98` | `−1.227` |

so `f < 0` throughout, the integral is *positive*, and it competes with the
negative boundary term — no one-sided shortcut. (This is consistent with the
classical fact that `ϑ(x) < x` up to around `1.4·10^9`.) This is numeric
evidence about a sign, not a proof of anything beyond `10^8`.

## What would actually work

The literature settles this, and it is *better* than "you need RH". Axler,
*Effective estimates for some functions defined over primes* (arXiv:2203.05917),
§6, attributes the following identity to Rosser–Schoenfeld p. 74 and reproduces
it verbatim:

```text
A₁(x) = (ϑ(x) − x)/(x log x) − ∫_x^∞ (ϑ(y) − y)(1 + log y)/(y² log² y) dy,      (6.1)
A₁(x) = Σ_{p≤x} 1/p − log log x − B,      B = γ + Σ_p (log(1−1/p) + 1/p),      (6.2)
```

— exactly the computation above (and note that `B` is the same constant our
nodes spell out as `γ + Σ'_p (log (1−1/p) + 1/p)`). The same source quotes
R–S **Theorem 5** as

```text
−1/(2 log²x) < A₁(x) < 1/(2 log²x)      (left: every x > 1; right: every x ≥ 286),
```

i.e. the sharp tier is `1/(2 log²x)`, and (6.1) involves **only `ϑ`** — the ψ
function is not needed at all.

Feed `|ϑ(y) − y| ≤ c·y/log^k y` into (6.1): the integral contributes
`c·∫_x^∞ (1+log y)/(y log^{k+2}y) dy = c(1/(k log^k x) + 1/((k+1)log^{k+1}x))`,
so

| `k` | input | resulting `|A₁(x)|` | verdict |
|---|---|---|---|
| 1 | `c·y/log y` (the platform's ψ node, `c = 1/40`) | `≈ 1/(40 log x)` | **too big** (the audit above) |
| 2 | `c·y/log²y` | `≈ c/(2log²x)` | reaches the R–S tier once `c ≲ 0.49` |
| 4 | `57.184·y/log⁴y` (see below) | `7.2·10^-6` at `x = 10^8` | **200× margin** on `1.4724·10^-3` |

For `k = 2` the exact sufficient condition at `log x ≥ 18.42` is
`c(1 + 1/(3log x) + 1/(4log²x)) ≤ 1/2 − 1/(8log²x)`, i.e. `c ≤ 0.490`.

**So the correct input is any explicit θ estimate with at least two powers of
`log` in the denominator**, and the literature supplies one with four. Axler §3
tabulates (as (3.5), for every `x ≥ 1 091 159`)

```text
|ϑ(x) − x| ≤ 57.184 · x / log⁴x ,
```

with Dusart's Corollary 5.5 improving the constant; Axler's own sharpest
Chebyshev input is `|ϑ(x) − x| < 0.024334 x/log³x` for `x ≥ 1 757 126 630 797`.
With the four-log form, `|A₁(x)| ≤ 57.184(1/log⁵x)(1/5 + 1/(6log x) + 1/log x)
= 7.2·10^-6` at `x = 10^8`, and it *improves* with `x` (the bound is `≍1/log⁵x`
while the allowance is `≍1/(2log²x)`).

**Caveat on the exact right-hand side.** `A`/`A*` ask for
`log(1 + 1/(2log²x))`, which is *stronger* than the standard quote
`1/(2log²x)` (as `log(1+z) < z`). The θ route above delivers `7·10^-6`, far
below both, so it proves `A`/`A*` as stated — but someone closing
`product_log_bound_large` by *citing* R–S Theorem 5 alone gets only
`Σ log(p/(p−1)) < γ + log log x + 1/(2log²x)`, which does **not** imply the
node's `log(1 + 1/(2log²x))` (the gap is `≈ 1/(8log⁴x)`); that form needs the
product-side statement instead. The two are not interchangeable.

## Recommendation

> **Superseded, 23:55.** Recommendation (2) below (publish a θ node with a
> `57.184 x/log⁴x` bound and derive the reciprocal bound from it by Abel
> summation) is **not needed**. Mawia's *Explicit Mertens sums* (2017) is
> *directly* a bound on `Σ_{p≤x}1/p` — `|A₁(x)| ≤ 4/log³x` for `x ≥ 2` — which
> dominates `A`/`A*` after the one elementary step `log(1+z) ≥ z/(1+z)`, with no
> formalisation of the identity and no Chebyshev input at all. That node is
> published as `TaoFivePrimes.mawia_reciprocal_sum_bound` (`a182289a`), and both
> reciprocal nodes are reduced to it (`SKETCH_ACCEPTED`, submissions `512a35d6`
> and `ebbdeec3`). Items (1), (3) and (4) below stand unchanged; the computation
> in this file is still the reason the Chebyshev route had to be abandoned.

1. **Do not attempt** `reciprocal_prime_sum_upper_bound{,_strict}` from
   `schoenfeld_psi_error_large`. It cannot work: that node has `1/log` decay,
   Abel summation needs at least `1/log²` (crossover at `x = 1.0668·10^8`, i.e.
   it fails essentially immediately).
2. The landable route is: **publish a θ node with a `1/log⁴` (or `1/log²`-with
   a small constant) error bound** — e.g.
   ```lean
   theorem theta_error_four_logs (y : ℝ) (hy : 1.091159e6 ≤ y) :
       |Chebyshev.theta y - y| ≤ 57.184 * y / (Real.log y) ^ 4
   ```
   — and reduce `A` / `A*` to it via identity (6.1) plus elementary integral
   bounds. ⚠️ Pin the citation down before publishing: the `57.184 x/log⁴x`
   bound is quoted by Axler as [10] table 15 (Trudgian / Broadbent et al.),
   with Dusart's Corollary 5.5 an improvement.
3. Treat the existing `A` / `A*` nodes as **external-quote tier** until (2) is
   done — the same tier as `TaoFivePrimes.liu_wang_three_primes`.
4. The rest of the product-log branch is unaffected: `B`
   (`mertens_tail_le_partial_sum`) is **Proved** and the reduction
   `Sol_TaoFivePrimes_rosser_schoenfeld_product_log_bound_large.lean` is ready
   and signature-matched.

## Reproduction

```bash
python tmp/check_reciprocal_prime_sum.py   # A_1(x) and the route bound, sieve to 10^8, ~3 s, no dependencies
python tmp/check_theta_sign.py             # theta(x) - x and its sign, same sieve
```

Both are dependency-free (`bytearray` sieve + `math.fsum`), 3–4 s each. Outputs
the tables above. Everything else in this note is elementary algebra by hand; the
identity (6.1) and R–S Theorem 5 are quoted from Axler, arXiv:2203.05917, §6 /
§1 (which in turn cites R–S 1962, p. 74 and Theorem 5).
