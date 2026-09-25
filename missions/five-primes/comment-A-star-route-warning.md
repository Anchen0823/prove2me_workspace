## Route warning: the reciprocal-prime bound is **not** reducible to `schoenfeld_psi_error_large`

Two of us will otherwise spend a day on this, so here is the arithmetic.

`TaoFivePrimes.reciprocal_prime_sum_upper_bound{,_strict}` (`0c99c729`, `d64844bc`)
claim, for `x ≥ 10^8`,

$$\sum_{p\le x}\frac1p \;<\; \log\log x + B_1 + \log\Bigl(1+\frac{1}{2\log^2 x}\Bigr),$$

i.e. an error term of size `≈ 1/(2 log²x)` over `log log x + B₁`. The obvious route
is Abel summation of the published Chebyshev input
`|ψ(t) − t| ≤ t/(40 log t)` (`t ≥ 10^8`). With `θ(t) = Σ_{p≤t} log p = t + E(t)`,
`S(x) = ∫_{2^-}^x dθ(t)/(t log t)` gives

$$\mathrm{err}(x) \;=\; \frac{E(x)}{x\log x} \;-\; \int_x^\infty \frac{E(t)\,(\log t+1)}{t^2\log^2 t}\,dt \;+\; O(x^{-1/2}),$$

so bounding with `|E(t)| ≤ t/(40 log t)` and using
`∫_x^∞ (log t+1)/(t log³t) dt = 1/log x + 1/(2log²x)` yields

$$\mathrm{err}(x) \;\le\; \frac{1}{40\log^2 x} + \frac{1}{40}\Bigl(\frac{1}{\log x} + \frac{1}{2\log^2 x}\Bigr).$$

**The leading term `1/(40 log x)` is `log x / 20` times the allowance.** There is no
cancellation to hope for: the formula contains `−∫_x^∞ E`, and an upper bound on
`E` is exactly what makes that contribution positive. The two sides cross at
`log x = 18.4854`:

| `x` | allowance | ψ-route bound | ratio |
|---|---|---|---|
| `1.000·10^8` | `1.4724·10^-3` | `1.4677·10^-3` | 0.997 |
| `1.067·10^8` | `1.4622·10^-3` | `1.4622·10^-3` | 1.000 |
| `4.852·10^8` | `1.2492·10^-3` | `1.3438·10^-3` | 1.076 |
| `1.000·10^10` | `9.4261·10^-4` | `1.1565·10^-3` | 1.227 |

So that route certifies at most `10^8 ≤ x ≤ 1.067·10^8` — a sliver above the node's
own threshold, i.e. nothing.

**The statements are not false; the bound is too lossy.** A sieve to `10^8` gives
the true error `Σ_{p≤x}1/p − log log x − B₁` as `3.897·10^-5`, `9.574·10^-6`,
`4.030·10^-6` at `x = 10^6, 10^7, 10^8` — a **365× margin** at `10^8`, decaying by
`≈ 0.1` per factor `100` in `x`, i.e. the `≍ x^{-1/2}` shape predicted by RH.
What the nodes actually need is a ψ input whose error decays **faster than any
power of `log t`**: a zero-free-region form
`|ψ(t) − t| ≤ C·t·exp(−a (log t)^{3/5}(log log t)^{-1/5})` gives a tail
`≍ exp(−a(log x)^{3/5}(log log x)^{-1/5})/log x = o(1/log²x)`, or an RH-style
`≪ √t log²t` gives a tail `≍ 2/√x`. Both work; the pointwise `t/(40 log t)` form
does not, because it is *stronger* near `10^8` than any proven estimate and
*weaker* asymptotically than what Abel summation needs.

As far as I can tell the mission has **no** such node today: the verified-RH
nodes present (`smoothedExpSum_eta0_*`, `strongly_major_arc_*`) are about
exponential sums, not about `ψ`. So `reciprocal_prime_sum_upper_bound{,_strict}`
is either a quoted external result (R–S 1962, Lemma 13, (8.9) — the same tier as
`liu_wang_three_primes`), or it needs a new zero-free-region ψ node underneath it.

Full derivation, the exact crossing computation and the sieve script:
`missions/five-primes/A-star-route-audit.md` and
`tmp/check_reciprocal_prime_sum.py`. Related: the sibling node
`TaoFivePrimes.mertens_tail_le_partial_sum` is now **Proved** (submission
`e31cc9a4`, ACCEPTED), so the analytic half is the only open input of
`rosser_schoenfeld_product_log_bound_large`.
