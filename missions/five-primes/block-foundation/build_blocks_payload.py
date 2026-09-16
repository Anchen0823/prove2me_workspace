#!/usr/bin/env python
"""Build the /submit-definition payload for the *extended* block foundation.

The first publication `TaoFivePrimes_BlockFoundation` carried only the
§1-5 foundation.  This payload carries the three-layer module
(`Definitions/Def_TaoFivePrimes_BlockFoundation.lean`: foundation,
block structure, frozen envelope) under a new definition name so it does
not collide with the already-published one.
"""
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
SRC = os.path.join(ROOT, "Definitions", "Def_TaoFivePrimes_BlockFoundation.lean")
OUT = os.path.join(ROOT, "missions", "five-primes", "block-foundation",
                   "definition-blocks-payload.json")

NL = r"""**The full reusable interface for Tao's Type I block summation.**

This module collects the three layers of Tao's Section 5 argument
(arXiv:1201.6656v4, the passage (5.14) → (5.17)) that are independent of
any particular exponential-sum input.

**§1-5 — integer distance and the sine envelope.** With $\|t\|_{\mathbb R/\mathbb Z}$ the distance from $t$ to the nearest integer, realized as `rdist t = min (Int.fract t) (1 - Int.fract t)`:

$$2\,\|t\|_{\mathbb R/\mathbb Z}\ \le\ |\sin(\pi t)|\ \le\ \pi\,\|t\|_{\mathbb R/\mathbb Z}. \tag{2.1}$$

The lower and upper halves are `two_rdist_le_abs_sin` and
`abs_sin_le_pi_mul_rdist`. The module also proves `rdist` is a genuine
metric pseudo-norm (§4: `rdist_add_le'`, `rdist_add_le`,
`rdist_sub_le_abs_sub`), that `q \nmid m` forces
$\|m/q\|_{\mathbb R/\mathbb Z} \ge 1/q$ (`rdist_div_ge`), and the
small-$d$ quantitative core of (5.15): if $4\alpha = a/q + \beta$ with
$|\beta| \le q^{-2}$, $2d \le q$ and $q \nmid ad$, then
$\|4d\alpha\|_{\mathbb R/\mathbb Z} \ge \frac{1}{2q}$
(`rdist_d_alpha_ge`). Together with (2.1) this yields the uniform bound
$|\sin(2\pi d\alpha)| \ge 1/q$, i.e. $1/|\sin(2\pi d\alpha)| \le 2q$, on
$d \le q/2$.

**§6-7 — the block structure.** `blockLeft q j = 2jq + \tfrac q2` and
`blockRight q j = 2(j+1)q + \tfrac q2` are the block endpoints; their
difference is exactly $2q$ (`blockRight_sub_blockLeft`), which is what
makes the harmonic sum over blocks comparable with an integral. The two
endpoint lemmas translate between the *doubled integer spacing*
$4jq + q < 2d \le 4(j+1)q + q$ and the real interval
$\mathrm{blockLeft}\,q\,j < d \le \mathrm{blockRight}\,q\,j$, and
`mem_block_iff` states the equivalence.

**§8 — the frozen envelope.** On a block, the pointwise envelope
$\frac12\frac xd\log x + 4(\log 2)\log 2x$ is increasing as $d$ decreases,
so it is dominated by its value at the left endpoint; since the node's
envelope is a `min` of two alternatives, freezing the $\frac xd$ term while
retaining the cosecant term is legitimate. This is `freeze_x_div` together
with `envelope_frozen_vanish` / `envelope_frozen_nonvanish`, the two cases
of the sine vanishing or not.

**Formalization Note.** Everything is `sorry`-free and Mathlib-only.
The block endpoint statements are stated in doubled integer form because
`linarith` treats $\uparrow q/2$ as an opaque atom; the halving is done
once by `div_lt_iff₀` after a `ring` normalization. No `conv` is used
anywhere (rewriting under `abs`/`Real.sin` via `conv_rhs` exhausts the
heartbeat budget in this environment).
"""


def main():
    with open(SRC, "r", encoding="utf-8") as fh:
        body = fh.read()
    payload = {
        "definition_name": "TaoFivePrimes_BlockFoundationBlocks",
        "definition_title": "Tao Type I block summation: integer distance, (2.1), block structure, frozen envelope",
        "definition": body,
        "natural_language_statement": NL,
        "source": (
            "Terence Tao, \"Every odd number greater than 1 is the sum of at most five primes\", "
            "Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, "
            "https://arxiv.org/abs/1201.6656, Section 5, the block decomposition (5.14)-(5.17), "
            "and Section 2, inequality (2.1)."
        ),
        "tags": ["analytic-number-theory", "exponential-sums", "goldbach", "number-theory"],
    }
    with open(OUT, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, ensure_ascii=False, indent=2)
    print("wrote", OUT, len(body), "bytes of Lean")


if __name__ == "__main__":
    main()
