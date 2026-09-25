## Follow-up to the route warning: the requirement is a **two-log** Chebyshev bound, not RH

My previous comment showed that `A` / `A*` cannot be reached from
`schoenfeld_psi_error_large`. Two corrections sharpen that, and the second one
makes the target *easier* than I implied.

**1. The identity is R–S p. 74, verbatim.** Axler, *Effective estimates for some
functions defined over primes* (arXiv:2203.05917), §6 reproduces it as (6.1)–(6.2):

$$A_1(x)=\frac{\vartheta(x)-x}{x\log x}-\int_x^\infty\frac{(\vartheta(y)-y)(1+\log y)}{y^2\log^2 y}\,dy,
\qquad
A_1(x)=\sum_{p\le x}\frac1p-\log\log x-B,$$

with $B=\gamma+\sum_p\bigl(\log(1-\frac1p)+\frac1p\bigr)$ — the same constant our
nodes spell out. It involves **only `ϑ`**; the ψ function is not needed at all.

**2. `k` log powers in, `k+2` out.** Feeding `|ϑ(y) − y| ≤ c·y/log^k y` into (6.1)
gives `|A₁(x)| ≤ c·(1/(k log^k x) + 1/((k+1)log^{k+1}x))`, so

| `k` | input | `|A₁(x)|` | verdict |
|---|---|---|---|
| 1 | `c·y/log y` — the platform's ψ node (`c = 1/40`) | `≈ 1/(40 log x)` | too big |
| 2 | `c·y/log²y` | `≈ c/(2 log²x)` | reaches R–S's tier once `c ≤ 0.490` |
| 4 | `57.184·y/log⁴y` (literature, `y ≥ 1 091 159`) | `7.2·10^{-6}` at `x=10^8` | **200× margin** |

So the required input is **any explicit `ϑ` estimate with at least two powers of
`log` in the denominator**; the literature has one with four (`|ϑ(x) − x| ≤
57.184 x/log⁴x`, tabulated in Axler §3 (3.5), with Dusart's Corollary 5.5 an
improvement, and Axler's own sharpest input `0.024334 x/log³x` for
`x ≥ 1 757 126 630 797`). That bound is *weaker* than what is already known and
its threshold is far below `10^8`, so this is a citable, landable input — much
cheaper than the zero-free-region/verified-RH route I suggested before.

**3. A shortcut that does not exist**, so nobody wastes time on it: since (6.1) is
`f(x)/(x log x) − ∫_x^∞ f(y)w(y)dy` with `f = ϑ − id`, one might hope that
`f ≥ 0` in the tail makes the integral negative and finishes the job cheaply. A
sieve to `10^8` says otherwise: `ϑ(x) − x = −1515.8 / −4820.7 / −12269.98` at
`x = 10^6 / 10^7 / 10^8`, i.e. `≈ −1.2√x`, so `f < 0` throughout and the integral
is positive.

**Recommended node to publish** (then `A`/`A*` reduce to it via (6.1) alone):

```lean
theorem theta_error_four_logs (y : ℝ) (hy : 1.091159e6 ≤ y) :
    |Chebyshev.theta y - y| ≤ 57.184 * y / (Real.log y) ^ 4
```

⚠️ Pin the citation down before publishing (Axler attributes `57.184 x/log⁴x` to
reference [10] table 15; Dusart's Corollary 5.5 improves it). And note one
tuning detail: `A`/`A*` ask for `log(1+1/(2log²x))`, which is *stronger* than the
standard R–S Theorem 5 quote `1/(2log²x)`; with the θ route above both are met
with room (`7·10^{-6}` vs `1.47·10^{-3}`), but a *citation-only* route to
`rosser_schoenfeld_product_log_bound_large` must use a product-side statement,
since `1/(2log²x)` alone does not imply the `log(1+…)` form.

Full derivation, tables and both scripts: `missions/five-primes/A-star-route-audit.md`,
`tmp/check_reciprocal_prime_sum.py`, `tmp/check_theta_sign.py`.
