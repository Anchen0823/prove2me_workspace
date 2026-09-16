#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""Payload for the sharp Vinogradov interface definition."""
import json
import os

ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.normpath(
    os.path.join(HERE, "..", "..", "..", "examples", "five-primes",
                 "Theorem51VinogradovSharp.lean")
)

with open(SRC, encoding="utf-8") as fh:
    definition = fh.read()

NL = r"""**The odd-restricted Vinogradov estimate at the sharp block count, together with the reflection that halves the one-sided odd sum.**

This module is the interface layer between the block estimate of the source's Lemma 3.4 and the Type I block summation of Section 5.2. It contains no analysis: the classical estimate itself enters as a `Prop`-valued hypothesis. What is proved here are the two index-manipulations that decide the constant in the source's display (5.17).

**§1 The summand.** Write

$$\mathrm{vmin}(A,B,\alpha,\theta;n)\ :=\ \begin{cases}A,&\sin(\pi\alpha n+\theta)=0,\\ \min\!\Bigl(A,\frac B{|\sin(\pi\alpha n+\theta)|}\Bigr),&\text{otherwise.}\end{cases}$$

The convention at the zeros of the sine is the source's, and is forced: at a vanishing phase the minimum equals $A$, whereas a bare $\min$ would return $\min(A,B/0)=0$ under the ambient division convention. Two symmetries are recorded. Under $n=2m+1$ the phase transforms by

$$\pi\alpha(2m+1)+\theta=\pi(2\alpha)m+(\pi\alpha+\theta),$$

i.e. the frequency doubles and the phase shifts by $\pi\alpha$ (`vmin_odd`); and for $\theta=0$ the summand is even in $n$ (`vmin_neg`).

**§2 The reindexing.** For real endpoints $x<y$ let $(x,y]_{\mathbb Z}$ denote the integers $z$ with $x<z\le y$. Then for every $m\in\mathbb Z$,

$$2m+1\in(x,y]_{\mathbb Z}\iff m\in\Bigl(\tfrac{x-1}2,\tfrac{y-1}2\Bigr]_{\mathbb Z},$$

with **no** side condition (`odd_mem_zIoc_iff`), and consequently

$$\sum_{\substack{z\in(x,y]_{\mathbb Z}\\ z\ \mathrm{odd}}} f(z)=\sum_{m\in(\frac{x-1}2,\frac{y-1}2]_{\mathbb Z}} f(2m+1)$$

(`odd_sum_reindex`). Both statements are made over $\mathbb Z$ rather than $\mathbb N$ on purpose: `Int.floor` is not clamped at zero, so the first equivalence is exact, whereas over $\mathbb N$ it needs the hypothesis $1\le x$ and, worse, the reflection below becomes inexpressible.

**§3 The sharp block count.** Let

$$R(q,A,B)\ :=\ 2A+\frac2\pi Bq\log 4q .$$

`blockBound` is the assertion that $\sum_{n\in(x,y]_{\mathbb Z}}\mathrm{vmin}\le R$ whenever $y-x\le q$, and `oddBlockBound` that the same holds for the *odd* integers whenever $y-x\le 2q$. The passage from the first to the second is `odd_block_from_block`: the reindexing halves the width, so a range of width $2q$ of odd integers becomes a range of width $q$ of all integers, and one application of the block estimate suffices.

This is where the constant of (5.17) is decided. The source's Corollary 3.5 as published carries the covering count $\lfloor\frac{y-x}{2q}\rfloor+1$, which on a block of width exactly $2q$ — the case used in Section 5.2 — evaluates to $\lfloor1\rfloor+1=2$. That count over-counts: the number of blocks of length $L$ needed to cover a range of width $W$ is $\lceil W/L\rceil$, and $\lfloor W/L\rfloor+1$ exceeds it precisely when $L\mid W$. The correct count here is $1$, and it is what the source's own proof produces, since it applies Lemma 3.4 to the reindexed range of width $q$. Carrying the published count instead doubles the constant of (5.17) from $0.89$ to $1.78$.

**§4 The reflection.** Because the summand is even and the odd integers of $[-M,M]$ are exactly the odd integers of $[1,M]$ together with their negatives,

$$\sum_{\substack{-M\le z\le M\\ z\ \mathrm{odd}}} g(z)=2\sum_{\substack{1\le z\le M\\ z\ \mathrm{odd}}} g(z)$$

(`odd_symm_sum`), and hence, when $2M+1\le2q$,

$$\sum_{\substack{1\le z\le M\\ z\ \mathrm{odd}}}\mathrm{vmin}(A,B,\alpha,0;z)\ \le\ A+\frac1\pi Bq\log4q,$$

half of $R(q,A,B)$ (`odd_symm_min_sum_le`). This is the step behind the source's "by symmetry we may thus bound the contribution of the $d\le q/2$ terms": applied with $A=2q$, $B=1$, $M=\lfloor q/2\rfloor$ it gives $2q+\frac1\pi q\log4q$, which is half of the $4q+\frac2\pi q\log4q$ that Corollary 3.5 returns on the symmetric range. The halving is not optional. It is exactly what converts the block-count slack $\frac{UV}{2q}+\frac34$ into the source's $\frac{UV}{2q}+\frac54$, and without it the assembled bound exceeds the Type I right-hand side by a factor $1.29$ in the worst admissible corner.

**§5 The cast bridge.** The Type I node sums over the positive odd *naturals* $d\le UV$; the estimates above live on $\mathbb Z$. `nat_odd_iff_int_odd` and `sum_nat_odd_eq_int_odd` identify the two sums along $d\mapsto(d:\mathbb Z)$.

**Formalization note.** Everything is `sorry`-free and Mathlib-only, with the only axioms `propext`, `Classical.choice`, `Quot.sound`. The endpoints are kept as real numbers throughout and the integer intervals are realized as `Finset.Icc (⌊x⌋+1) ⌊y⌋`, so that no floor identity has to be re-derived at the point of use. `blockBound_of_int_block` converts the platform's formulation of the block estimate (on `Finset.Ioc m (m+q)` for integer $m$) into `blockBound`; it uses nonnegativity of the summand to pass from the larger integer block to the sub-range actually needed.
"""

payload = {
    "env": ENV,
    "definition_name": "TaoFivePrimes_Theorem51VinogradovSharp",
    "definition_title": "Odd Vinogradov estimate at the sharp block count, with the reflection halving",
    "definition": definition,
    "natural_language_statement": NL,
    "source": (
        'Terence Tao, "Every odd number greater than 1 is the sum of at most five '
        'primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656v4, '
        'Lemma 3.4 and Corollary 3.5 (pp. 13-14) and their use in Section 5.2, '
        'equations (5.14)-(5.17), in particular the display '
        '"by Corollary 3.5 one has ... so by symmetry we may thus bound the '
        'contribution of the d <= q/2 terms by 2 log 2 log 2x ((2/pi) q log 4q + 4q)". '
        'https://arxiv.org/abs/1201.6656'
    ),
    "tags": ["analytic-number-theory", "exponential-sums", "goldbach", "number-theory"],
}

out = os.path.join(HERE, "definition-vinogradov-sharp-payload.json")
with open(out, "w", encoding="utf-8") as fh:
    json.dump(payload, fh, ensure_ascii=False, indent=1)
print("wrote", out, len(definition), "bytes of Lean")
