#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""Payload + reduction for `TaoFivePrimes.vinogradov_odd_sharp`.

This is Corollary 3.5 at the *sharp* block count: a single block of width `2q`
of odd integers costs `2A + (2/pi) B q log 4q`, not twice that.
"""
import json
import os

ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
HERE = os.path.dirname(os.path.abspath(__file__))

SOURCE = (
    'Terence Tao, "Every odd number greater than 1 is the sum of at most five '
    'primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656v4, '
    'Corollary 3.5 (p. 13) and its proof ("Writing n = 2m + 1, the expression on '
    'the left-hand side is ...; the claim then follows from Lemma 3.4"), together '
    'with the use made of it in Section 5.2 on the blocks '
    '2jq + q/2 < d <= 2(j+1)q + q/2. https://arxiv.org/abs/1201.6656'
)
TAGS = ["analytic-number-theory", "exponential-sums", "goldbach", "number-theory"]
PREAMBLE = ("import Mathlib\n"
            "import Definitions.Def_TaoFivePrimes_Theorem51VinogradovSharp\n\n"
            "open Finset\nopen TaoFivePrimesVinogradovSharp")

STMT = """theorem TaoFivePrimes.vinogradov_odd_sharp
    (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 0 < q)
    (A alpha beta theta x y : ℝ) (a' : ℤ) (hA : 0 ≤ A)
    (ha'q : Nat.Coprime a'.natAbs q)
    (halpha : 2 * alpha = (a' : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hwidth : y ≤ x + 2 * (q : ℝ)) :
    (∑ z ∈ (TaoFivePrimesVinogradovSharp.zIoc x y).filter (fun z => Odd z),
        TaoFivePrimesVinogradovSharp.vmin A B alpha theta z)
      ≤ 2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q) := by
  sorry"""

NL = r"""**Corollary 3.5 at the sharp block count: a range of odd integers of width $2q$ costs one block, not two.**

Let $q\ge1$, let $A\ge0$ and $B\ge0$, let $a'$ be an integer coprime to $q$, and let

$$2\alpha=\frac{a'}q+\beta,\qquad |\beta|\le q^{-2}.$$

Then for all real $\theta$ and all real endpoints $x<y$ with $y-x\le 2q$,

$$\sum_{\substack{z\in(x,y]_{\mathbb Z}\\ z\ \mathrm{odd}}}\ \mathrm{vmin}(A,B,\alpha,\theta;z)\ \le\ 2A+\frac2\pi Bq\log 4q,$$

where $\mathrm{vmin}(A,B,\alpha,\theta;z)$ is $A$ when $\sin(\pi\alpha z+\theta)=0$ and $\min\bigl(A,\frac B{|\sin(\pi\alpha z+\theta)|}\bigr)$ otherwise.

This is the source's Corollary 3.5 restricted to the case that actually occurs in Section 5.2, and the restriction matters. As published, Corollary 3.5 carries the covering count $\lfloor\frac{y-x}{2q}\rfloor+1$. On a block $2jq+\frac q2<d\le2(j+1)q+\frac q2$, whose width is exactly $2q$, that count evaluates to $\lfloor1\rfloor+1=2$; but the number of blocks of length $L$ needed to cover a range of width $W$ is $\lceil W/L\rceil$, and $\lfloor W/L\rfloor+1$ exceeds it exactly when $L$ divides $W$. Here $L=2q$ and $W=2q$, so the correct count is $1$.

The source's own proof produces the sharp count. Writing $n=2m+1$ turns the left-hand side into

$$\sum_{\frac{x-1}2<m\le\frac{y-1}2}\mathrm{vmin}\bigl(A,B,2\alpha,\pi\alpha+\theta;m\bigr),$$

because $\pi\alpha(2m+1)+\theta=\pi(2\alpha)m+(\pi\alpha+\theta)$. The $m$-range has width $\frac{y-x}2\le q$, so Lemma 3.4 applies to it with **one** block. The doubling of the admissible width from $q$ to $2q$ and the doubling of the frequency from $\alpha$ to $2\alpha$ are the same phenomenon seen from the two sides of the reindexing; nothing in the argument asks for two blocks.

The constant is decided here. Carrying the published count instead of the sharp one doubles the coefficient of the second term of the source's display (5.17) from $0.89$ to $1.78$, and the platform's Type I right-hand side does not accommodate that: the assembled bound then overshoots by a factor $1.29$ in the worst admissible corner.

**Formalization note.** The summation range is $(x,y]_{\mathbb Z}$, realized as `zIoc`, and the summand uses the explicit `if` convention at the zeros of the sine, since Lean's real division returns $0$ there and a bare `min` would silently contribute $0$ instead of $A$. The reindexing is stated over $\mathbb Z$ rather than $\mathbb N$ because `Int.floor` is not clamped at zero, which makes the index-set identity exact and, more importantly, makes the reflection argument (`odd_symm_min_sum_le`, in the same definition module) expressible at all. The hypothesis $2\alpha=\frac{a'}q+\beta$ is exactly the hypothesis of Corollary 3.5 as stated in the source.
"""

payload = {
    "env": ENV,
    "problems": [{
        "theorem_name": "TaoFivePrimes.vinogradov_odd_sharp",
        "theorem_title": "Odd-restricted Vinogradov estimate at the sharp block count (source Corollary 3.5)",
        "formal_statement": STMT,
        "preamble": PREAMBLE,
        "natural_language_statement": NL,
        "source": SOURCE,
        "tags": TAGS,
    }],
}
out = os.path.join(HERE, "odd-sharp-payload.json")
with open(out, "w", encoding="utf-8") as fh:
    json.dump(payload, fh, ensure_ascii=False, indent=1)
print("wrote", out)

# ---- the reduction -------------------------------------------------------
REDUCTION = """import Mathlib
import Definitions.Def_TaoFivePrimes_Theorem51VinogradovSharp
import Theorems.Thm_TaoFivePrimes_vinogradov_block_coprime

open Finset
open TaoFivePrimesVinogradovSharp

/-- Corollary 3.5 at the sharp block count, from the corrected block estimate. -/
theorem solution
    (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 0 < q)
    (A alpha beta theta x y : ℝ) (a' : ℤ) (hA : 0 ≤ A)
    (ha'q : Nat.Coprime a'.natAbs q)
    (halpha : 2 * alpha = (a' : ℝ) / q + beta) (hbeta : |beta| ≤ 1 / (q : ℝ) ^ 2)
    (hwidth : y ≤ x + 2 * (q : ℝ)) :
    (∑ z ∈ (TaoFivePrimesVinogradovSharp.zIoc x y).filter (fun z => Odd z),
        TaoFivePrimesVinogradovSharp.vmin A B alpha theta z)
      ≤ 2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q) := by
  have hR : vRhs q A B = 2 * A + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q) := by
    unfold vRhs
    norm_num
  have hbb : blockBound q A B (2 * alpha) (Real.pi * alpha + theta) ((x - 1) / 2) ((y - 1) / 2) :=
    blockBound_of_int_block q A B (2 * alpha) (Real.pi * alpha + theta)
      ((x - 1) / 2) ((y - 1) / 2) hA hB
      (fun m => by
        simpa [vmin, hR] using
          (TaoFivePrimes.vinogradov_block_coprime B hB q hq A (2 * alpha) beta
            (Real.pi * alpha + theta) a' hA ha'q halpha hbeta m))
  have hodd := odd_block_from_block q A B alpha theta x y hbb hwidth
  simpa [hR] using hodd
"""
red_out = os.path.normpath(
    os.path.join(HERE, "..", "..", "..", "Solutions", "Sol_vinogradov_odd_sharp.lean"))
with open(red_out, "w", encoding="utf-8") as fh:
    fh.write(REDUCTION)
print("wrote", red_out)
