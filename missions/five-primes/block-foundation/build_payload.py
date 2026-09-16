#!/usr/bin/env python
"""Build the /submit-definition payload for the Type I block foundation.

Reads the locally compiled, sorry-free
`examples/five-primes/Theorem51BlockFoundation.lean` and wraps it as the
platform definition `Def_TaoFivePrimes_BlockFoundation`, so the submitted
body is byte-identical to what was verified locally with
`lake env lean`.
"""
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
SRC = os.path.join(ROOT, "examples", "five-primes", "Theorem51BlockFoundation.lean")
OUT = os.path.join(ROOT, "missions", "five-primes", "block-foundation", "definition-payload.json")

NL = r"""**Distance to the nearest integer and the sine envelope.**

Write $\|t\|_{\mathbb R/\mathbb Z}$ for the distance from $t\in\mathbb R$ to the nearest integer, realized here as `rdist t = min (Int.fract t) (1 - Int.fract t)`, so that it always lies in $[0,\tfrac12]$. This file establishes the elementary toolkit that Tao's Section 5 uses to pass from exponential sums to the envelope $\frac{4(\log 2)\log 2x}{|\sin(2\pi d\alpha)|}$:

* `rdist_nonneg`, `rdist_le_half` — range of the distance function;
* `rdist_add_le'`, `rdist_add_le`, `rdist_sub_le_abs_sub` — the triangle inequality, its $1$-Lipschitz form $\|x+y\|\le\|x\|+|y|$, and the reverse form $\|x\|-\|y\|\le\|x-y\|$;
* `abs_sin_pi_eq_abs_sin_pi_rdist`, `two_rdist_le_abs_sin`, `abs_sin_le_pi_mul_rdist` — **inequality (2.1)**, $\;2\|t\|_{\mathbb R/\mathbb Z}\le|\sin(\pi t)|\le\pi\|t\|_{\mathbb R/\mathbb Z}$, proved by reducing the sine phase modulo $\pi$ with $\sin(x+n\pi)=(-1)^n\sin x$;
* `div_q_eq`, `rdist_div_ge` — if $q\nmid m$ then $\|m/q\|_{\mathbb R/\mathbb Z}\ge 1/q$;
* `d_mul_beta_le`, `rdist_d_alpha_ge` — the small-$d$ quantitative core of **(5.15)**: if $4\alpha=a/q+\beta$ with $|\beta|\le q^{-2}$, $2d\le q$ and $q\nmid ad$, then $\|4d\alpha\|_{\mathbb R/\mathbb Z}\ge\frac1{2q}$, hence $|\sin(2\pi d\alpha)|\ge\frac1q$.

Together with (2.1) this is exactly the mechanism by which the target node converts the pointwise envelope on the range $d\le q/2$ into the uniform factor $2q$. All statements are `sorry`-free and depend only on Mathlib.
"""


def main():
    with open(SRC, "r", encoding="utf-8") as fh:
        body = fh.read()
    payload = {
        "definition_name": "TaoFivePrimes_BlockFoundation",
        "definition_title": "Type I block foundation: integer distance, inequality (2.1), and the small-$d$ core of (5.15)",
        "definition": body,
        "natural_language_statement": NL,
        "source": (
            "Terence Tao, \"Every odd number greater than 1 is the sum of at most five primes\", "
            "Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, "
            "https://arxiv.org/abs/1201.6656, Section 5, the small-$d$ regime of the "
            "Type I estimate, and Section 2, inequality (2.1)."
        ),
        "tags": ["analytic-number-theory", "exponential-sums", "goldbach", "number-theory"],
    }
    with open(OUT, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, ensure_ascii=False, indent=2)
    print("wrote", OUT, len(body), "bytes of Lean")


if __name__ == "__main__":
    main()
