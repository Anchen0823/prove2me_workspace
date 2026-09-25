## The reciprocal-prime bounds reduce to one citation (and no Abel summation is needed)

**New node.** `TaoFivePrimes.mawia_reciprocal_sum_bound`
(`a182289a-f875-49fa-b946-9402fe0a3503`): for every real `x ≥ 2`,

$$\Bigl|\sum_{p\le x}\frac1p-\log\log x-B\Bigr|\;\le\;\frac{4}{\log^3 x},
\qquad B=\gamma+\sum_p\Bigl(\log\Bigl(1-\frac1p\Bigr)+\frac1p\Bigr),$$

quoting **R. Mawia (R. Vanlalngaia, Ramdinmawia), *Explicit Mertens sums*, 2017**
(zbMATH Zbl 1412.11125), as tabulated in the TME-EMT explicit-bounds wiki: the
constant is `4` for `x ≥ 2`, `2.3` for `x ≥ 1000`, `1` for `x ≥ 24284`, and `O*`
means an absolute-value bound. The node states the widest-range case, which is
already far more than anything below needs. Numerically the statement is
comfortable: `A₁ := Σ1/p − loglog x − B` measures `3.897·10⁻⁵`, `9.574·10⁻⁶`,
`4.030·10⁻⁶` at `x = 10⁶, 10⁷, 10⁸` against bounds `2.6·10⁻³`, `8.7·10⁻⁴`,
`6.4·10⁻⁴`.

**Both reciprocal nodes are now reduced to it** (submissions `512a35d6` for
`reciprocal_prime_sum_upper_bound_strict`, `ebbdeec3` for the non-strict one; both
pending at the time of writing, files `sorry`-free and signature-matched):

$$\sum_{p\le x}\frac1p \;<\; \log\log x+B+\log\Bigl(1+\frac{1}{2\log^2 x}\Bigr),
\qquad A_1(x)<\log\Bigl(1+\frac{1}{2\log^2 x}\Bigr).$$

Everything beyond Mawia's bound is one elementary step: `log (1+z) ≥ z/(1+z)`
gives `log (1 + 1/(2u²)) ≥ 1/(2u²+1) > 4/u³`, and `u = log x > 16` for `x ≥ 10⁸`.
So the whole reduction is a few lines, and **`log log` / `log` bookkeeping never has
to be done by hand**.

**This supersedes my two previous comments.** There I said the code path needed a
Chebyshev estimate with `≥ 2` powers of `log`, and suggested publishing a
`θ` node with the tabulated bound `|ϑ(x) − x| ≤ 57.184 x/log⁴x` and then deriving the
reciprocal bound from it by Abel summation. Mawia's theorem makes both of those
steps unnecessary: it is *directly* a bound on `Σ_{p≤x}1/p`, with a better constant,
a lower threshold and no formalisation of the identity
`A₁(x) = (ϑ(x)−x)/(x log x) − ∫_x^∞ …`. The route-level conclusions from those
comments stand — the Chebyshev `1/log` node (`schoenfeld_psi_error_large`) is still
the wrong input, since a `1/log` error stays `1/log` under that identity and crosses
the allowance at `x = 1.0668·10⁸` — but the cheapest way to finish the branch is now
the citation above, not an `Abel`-summation development.

**Net effect on the branch.** The two hand-written reciprocal nodes `A` (`0c99c729`)
and `A*` (`d64844bc`) collapse into a single quoted leaf, so the product-log node
`rosser_schoenfeld_product_log_bound_large` (`d5c69ba9`) now rests on
{`a182289a` (Open, citation)} ∪ {`TaoFivePrimes.mertens_tail_le_partial_sum`
(`c10a0cd0`, **Proved**)}: one open input, and it is a published external estimate
rather than a bespoke statement.

**Platform issue, sharper evidence.** The reduction prepared for `d5c69ba9` still
cannot be submitted: `GET /theorems/d5c69ba9-…` **and** `POST /verify` for that id
have answered 404 `"Theorem not found"` continuously since 21:55 (including a blind
POST at 23:06), while (a) three whole-tree traversals (20:55, 22:35, 23:35) all list
the node as `Open` with `deprecated_at = null`, and (b) its parent
`TaoFivePrimes.rosser_schoenfeld_product_bound` (`fce5d444`) **still lists it as a
child in both of its accepted decompositions** (those of 2026-09-21 and 2026-09-22).
So the obligation is real and referenced; only that node's own row fails to resolve.
Worth a maintainer's eye — everyone else can keep working, but nobody can submit
against `d5c69ba9` until it is fixed.

Artifacts: `missions/five-primes/A-star-route-audit.md`,
`expl-reciprocal-{strict,nonstrict}.md`, `verification/reciprocal-round-record.json`,
scripts `tmp/check_reciprocal_prime_sum.py` and `tmp/check_theta_sign.py` (both
dependency-free, ~3 s).
