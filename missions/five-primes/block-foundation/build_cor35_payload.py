#!/usr/bin/env python
"""Build the /submit-definition payload for the Corollary 3.5 layer.

Publications so far:

  TaoFivePrimes_BlockFoundation       §1-5  (rdist, (2.1), (5.15) core)
  TaoFivePrimes_BlockFoundationBlocks §1-8  (+ block structure, frozen envelope)

This payload carries the *same* assembled module, which now also contains
the §9-12 Corollary 3.5 layer, under a fresh definition name
`TaoFivePrimes_BlockFoundationCor35` so it does not collide with the two
already-published names.  The Lean body is identical to the module that
`lake build Definitions.Def_TaoFivePrimes_BlockFoundation` compiles.
"""
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
SRC = os.path.join(ROOT, "Definitions", "Def_TaoFivePrimes_BlockFoundation.lean")
OUT = os.path.join(ROOT, "missions", "five-primes", "block-foundation",
                   "definition-cor35-payload.json")

NL = r"""**The reusable interface for Tao's Type I block summation, with the odd-restricted Vinogradov reduction.**

This module collects the layers of Tao's Section 5 argument
(arXiv:1201.6656v4, the passage (5.14) → (5.17)) that are independent of any
particular exponential-sum input, plus the reduction of Corollary 3.5 to
Lemma 3.4.

**§1-5 — integer distance and the sine envelope.** With $\|t\|_{\mathbb R/\mathbb Z}$ the distance from $t$ to the nearest integer, realized as `rdist t = min (Int.fract t) (1 - Int.fract t)`:

$$2\,\|t\|_{\mathbb R/\mathbb Z}\ \le\ |\sin(\pi t)|\ \le\ \pi\,\|t\|_{\mathbb R/\mathbb Z}. \tag{2.1}$$

Lower and upper halves are `two_rdist_le_abs_sin` and `abs_sin_le_pi_mul_rdist`. `rdist` is proved to be a genuine metric pseudo-norm (`rdist_add_le'`, `rdist_add_le`, `rdist_sub_le_abs_sub`); `q \nmid m` forces $\|m/q\|_{\mathbb R/\mathbb Z} \ge 1/q$ (`rdist_div_ge`); and the small-$d$ core of (5.15): if $4\alpha = a/q + \beta$, $|\beta| \le q^{-2}$, $2d \le q$, $q \nmid ad$, then $\|4d\alpha\|_{\mathbb R/\mathbb Z} \ge 1/(2q)$ (`rdist_d_alpha_ge`).

**§6-7 — the block structure.** `blockLeft q j = 2jq + q/2`, `blockRight q j = 2(j+1)q + q/2`, differing by exactly $2q$ (`blockRight_sub_blockLeft`), which is what makes the harmonic sum over blocks comparable with an integral. `blockLeft_lt_of` / `le_blockRight_of` translate between the doubled integer spacing $4jq + q < 2d \le 4(j+1)q + q$ and the real interval; `mem_block_iff` states the equivalence.

**§8 — the frozen envelope.** On a block the pointwise envelope $\frac12\frac xd\log x + 4(\log 2)\log 2x$ is dominated by its value at the left endpoint; since the node's envelope is a `min`, freezing the $\frac xd$ term while retaining the cosecant term is legitimate. This is `freeze_x_div` plus `envelope_frozen_vanish` / `envelope_frozen_nonvanish`.

**§9-12 — Corollary 3.5 from Lemma 3.4.** The published statements are recorded as the `Prop`-valued definitions `vinogradovMinSum` (Lemma 3.4) and `vinogradovMinSumOdd` (Corollary 3.5). The genuinely new content is the **reindexing**:

* `odd_mem_Ioc_iff`: for $1 \le x$, the odd integer $2m+1$ lies in $(x, y]$ exactly when $m$ lies in $((x-1)/2, (y-1)/2]$, i.e.
  $2m+1 \in \mathrm{Ioc}\,\lfloor x\rfloor\,\lfloor y\rfloor \iff \lfloor (x-1)/2\rfloor < m \le \lfloor (y-1)/2\rfloor$.
  The hypothesis $1 \le x$ is **not** removable: at $x=0, y=1$ the odd integer $1 = 2\cdot 0 + 1$ lies in $(0,1]$ but $\lfloor -1/2\rfloor < 0$ is false.
* `odd_min_sum_reindex`: `Finset.sum_bij` along $n \mapsto (n-1)/2$ identifies the odd min-sum with parameter $\alpha$ and phase $\theta$ with the full min-sum with parameter $2\alpha$ and phase $\pi\alpha + \theta$.
* `odd_vinogradov_min_sum`: Corollary 3.5 for $(\alpha, \theta)$ follows from Lemma 3.4 instantiated at $(2\alpha, \pi\alpha+\theta)$ on the shifted endpoints, since $(y-x)/(2q) = ((y-1)/2 - (x-1)/2)/q$.

Only this index arithmetic is proved; the analytic content of Lemma 3.4 (the Vinogradov bound) stays a hypothesis of the reduction.

**Formalization Note.** Everything is `sorry`-free and Mathlib-only, with the only axioms `propext`, `Classical.choice`, `Quot.sound`. Endpoint statements are stated in doubled integer form because `linarith` treats $\uparrow q/2$ as an opaque atom; the halving is done once by `div_lt_iff₀` after a `ring` normalization. No `conv` is used (rewriting under `abs`/`Real.sin` via `conv_rhs` exhausts the heartbeat budget in this environment). `Nat.floor_lt` requires an explicit `0 ≤ a` side condition, which is why the reindexing carries `1 ≤ x`.
"""


def main():
    with open(SRC, "r", encoding="utf-8") as fh:
        body = fh.read()
    payload = {
        "definition_name": "TaoFivePrimes_BlockFoundationCor35",
        "definition_title": "Tao Type I block summation: (2.1), block structure, frozen envelope, and Corollary 3.5 from Lemma 3.4",
        "definition": body,
        "natural_language_statement": NL,
        "source": (
            "Terence Tao, \"Every odd number greater than 1 is the sum of at most five primes\", "
            "Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, "
            "https://arxiv.org/abs/1201.6656, Section 5, the block decomposition (5.14)-(5.17) "
            "and the odd-restricted Vinogradov estimate (5.15)-(5.16); Section 2, inequality (2.1); "
            "Lemma 3.4 and Corollary 3.5."
        ),
        "tags": ["analytic-number-theory", "exponential-sums", "goldbach", "number-theory"],
    }
    with open(OUT, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, ensure_ascii=False, indent=2)
    print("wrote", OUT, len(body), "bytes of Lean")


if __name__ == "__main__":
    main()
