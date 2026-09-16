#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""Build the payload for the two corrected Vinogradov nodes.

The platform's `TaoFivePrimes.vinogradov_block_if_form` (00db332f) was
Disproved and `TaoFivePrimes.vinogradov_lemma_if_form` (15c69f72) is false for
the same reason: both omit the coprimality hypothesis gcd(|a'|, q) = 1.  These
two nodes restore it.
"""
import json
import os

ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
HERE = os.path.dirname(os.path.abspath(__file__))

SOURCE = (
    'Terence Tao, "Every odd number greater than 1 is the sum of at most five '
    'primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656v4, '
    'Lemma 3.4 and its proof ("By subdivision of the interval [x,y] it suffices to '
    'show that ... for all x"), together with the coprimality convention for the '
    'reduced fraction a/q used throughout Section 5 (see (5.15), where a=0 or '
    'q | a d would be excluded). https://arxiv.org/abs/1201.6656'
)

TAGS = ["analytic-number-theory", "exponential-sums", "goldbach", "number-theory"]

BLOCK_STMT = """theorem TaoFivePrimes.vinogradov_block_coprime
    (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 0 < q)
    (A' alpha' beta' theta' : ℝ) (a' : ℤ) (hA' : 0 ≤ A')
    (ha'q : Nat.Coprime a'.natAbs q)
    (halpha' : alpha' = (a' : ℝ) / q + beta') (hbeta' : |beta'| ≤ 1 / (q : ℝ) ^ 2)
    (m : ℤ) :
    (∑ n ∈ Finset.Ioc m (m + (q : ℤ)),
        (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
          else min A' (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
      ≤ 2 * A' + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q) := by
  sorry"""

BLOCK_NL = r"""**The single-block Vinogradov estimate, with the coprimality hypothesis restored.**

Let $q\ge1$, let $A'\ge0$ and $B\ge0$, let $a'$ be an integer **coprime to $q$**, and let $\alpha'=\frac{a'}{q}+\beta'$ with $|\beta'|\le q^{-2}$. Then for every real $\theta'$ and every integer $m$,

$$\sum_{m<n\le m+q}\ \mathrm{vmin}\Bigl(A',\frac{B}{|\sin(\pi\alpha'n+\theta')|}\Bigr)\ \le\ 2A'+\frac2\pi Bq\log 4q,$$

where $\mathrm{vmin}(A',t)$ denotes $A'$ when the sine vanishes and $\min(A',t)$ otherwise.

This is the inequality to which the source's Lemma 3.4 reduces by subdivision: Tao's proof says "by subdivision of the interval $[x,y]$ it suffices to show that $\sum_{x<n\le x+q}\min(A,\frac1{|\sin(\pi\alpha n+\theta)|})\le 2A+\frac2\pi q\log 4q$ for all $x$; the claim then follows from [8, Lemma 1]". It is the block estimate, not the subdivided one, that carries the analytic content, and it is stated here on its own so that the subdivision step (a purely combinatorial covering argument, already formalised as `TaoFivePrimes.vinogradov_lemma_if_form_from_block`) is separated from it.

**Why the coprimality hypothesis is needed.** The platform's `TaoFivePrimes.vinogradov_block_if_form` was **Disproved**, and `TaoFivePrimes.vinogradov_lemma_if_form` is false, for the same reason: without $\gcd(|a'|,q)=1$ the phase can be constant modulo $\pi$. For $a'=0$, $\beta'=\theta'=0$ one has $\sin(\pi\alpha'n+\theta')=0$ for every $n$, so each of the $q$ terms of a block contributes $A'$ while the right-hand side pays only $2A'$. With $\gcd(|a'|,q)=1$ the residues $a'n\bmod q$ run through all of $\mathbb Z/q\mathbb Z$ as $n$ runs over any $q$ consecutive integers, so the phase can vanish for at most one $n$ in the block; that single term is what the $2A'$ slot pays for.

**Formalization note.** The summand is written with an explicit `if` at the zeros of the sine rather than as a bare `min`: in Lean's real division $B/0$ is $0$, so `min A' (B/|sin|)` would silently contribute $0$ at a vanishing phase, whereas the source's convention (and the mathematically correct value of the minimum there) is $A'$. The block is the integer interval $(m,m+q]$, matching the shape that the subdivision lemma consumes. The variables $A',B,q$ are fixed first so that the statement can be used uniformly inside an induction over blocks.
"""

IF_STMT = """theorem TaoFivePrimes.vinogradov_lemma_if_form_coprime
    (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 0 < q)
    (A' alpha' beta' theta' u v : ℝ) (a' : ℤ) (hA' : 0 ≤ A')
    (ha'q : Nat.Coprime a'.natAbs q)
    (halpha' : alpha' = (a' : ℝ) / q + beta') (hbeta' : |beta'| ≤ 1 / (q : ℝ) ^ 2)
    (huv : u < v) :
    (∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋,
        (if Real.sin (Real.pi * alpha' * (n : ℝ) + theta') = 0 then A'
          else min A' (B / |Real.sin (Real.pi * alpha' * (n : ℝ) + theta')|)))
      ≤ ((⌊(v - u) / (q : ℝ)⌋ : ℤ) + 1)
          * (2 * A' + (2 / Real.pi) * B * (q : ℝ) * Real.log (4 * q)) := by
  sorry"""

IF_NL = r"""**Lemma 3.4 in the form the Type I argument consumes, with the coprimality hypothesis restored.**

Let $q\ge1$, let $A'\ge0$ and $B\ge0$, let $a'$ be an integer **coprime to $q$**, and let $\alpha'=\frac{a'}{q}+\beta'$ with $|\beta'|\le q^{-2}$. Then for all real $\theta'$ and all $u<v$,

$$\sum_{\lfloor u\rfloor<n\le\lfloor v\rfloor}\ \mathrm{vmin}\Bigl(A',\frac{B}{|\sin(\pi\alpha'n+\theta')|}\Bigr)\ \le\ \Bigl(\Bigl\lfloor\frac{v-u}{q}\Bigr\rfloor+1\Bigr)\Bigl(2A'+\frac2\pi Bq\log 4q\Bigr),$$

with $\mathrm{vmin}(A',t)=A'$ at a vanishing phase and $\min(A',t)$ elsewhere.

This is the source's Lemma 3.4, stated over the integer interval $(\lfloor u\rfloor,\lfloor v\rfloor]$. It differs from the platform's `TaoFivePrimes.vinogradov_lemma_if_form` (which is false as stated — see the Accepted disproof) only by the added hypothesis $\gcd(|a'|,q)=1$; that hypothesis is part of the classical statement, since the source writes $\alpha=a/q$ with $a/q$ a reduced fraction, and it is exactly what prevents the phase from being constant modulo $\pi$.

The proof is the source's: subdivide the range into $\lfloor\frac{v-u}{q}\rfloor+1$ consecutive blocks of length $q$ and apply the block estimate on each. The subdivision half is already formalised and proved as `TaoFivePrimes.vinogradov_lemma_if_form_from_block`; this node is the assembly of that with the corrected block estimate `TaoFivePrimes.vinogradov_block_coprime`.

**Formalization note.** The hypotheses $A'\ge0$ and $B\ge0$ are needed: for $A'<0$ the left side has one term per integer in the interval while the right side only counts blocks of length $q$. The convention at the zeros of the sine is made explicit by an `if`, since Lean's real division returns $0$ there.
"""

payload = {
    "env": ENV,
    "problems": [
        {
            "theorem_name": "TaoFivePrimes.vinogradov_block_coprime",
            "theorem_title": "Vinogradov block estimate with coprimality (source Lemma 3.4, block form)",
            "formal_statement": BLOCK_STMT,
            "preamble": "import Mathlib\n\nopen Finset",
            "natural_language_statement": BLOCK_NL,
            "source": SOURCE,
            "tags": TAGS,
        },
        {
            "theorem_name": "TaoFivePrimes.vinogradov_lemma_if_form_coprime",
            "theorem_title": "Vinogradov-type lemma with coprimality (source Lemma 3.4, interval form)",
            "formal_statement": IF_STMT,
            "preamble": "import Mathlib\n\nopen Finset",
            "natural_language_statement": IF_NL,
            "source": SOURCE,
            "tags": TAGS,
        },
    ],
}

out = os.path.join(HERE, "vinogradov-coprime-payload.json")
with open(out, "w", encoding="utf-8") as fh:
    json.dump(payload, fh, ensure_ascii=False, indent=1)
print("wrote", out)
