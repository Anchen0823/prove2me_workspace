#!/usr/bin/env python
"""Build the /submit-definition payload for the Assembly (Child 2) layer.

Publications so far:

  TaoFivePrimes_BlockFoundation         §1-5   (rdist, (2.1), (5.15) core)
  TaoFivePrimes_BlockFoundationBlocks   §1-8   (+ block structure, frozen envelope)
  TaoFivePrimes_BlockFoundationCor35    §1-12  (+ Corollary 3.5 from Lemma 3.4)

This payload carries the *assembly* module: the coprimality transfer, the
small-d cosecant bound (with the double-angle transfer to the node's
normalisation), the integral test, the block combinatorics (coverage,
uniqueness, disjointness, telescoping biUnion), and the envelope split that
reduces the node's `min` envelope to a sum of two easily bounded pieces.

Platform definitions are compiled **standalone** — `import
Definitions.Def_...` is not resolvable there — so the payload must concatenate
every local dependency:

    Definitions.Def_TaoFivePrimes_BlockFoundation   (rdist, (2.1), (5.15), blocks,
                                                     frozen envelope, Cor 3.5)
    Definitions.Def_TaoFivePrimes_Theorem51Sums     (the divisor interface)
    Definitions.Def_TaoFivePrimes_Theorem51Assembly (this module)

Only the first `import Mathlib`-style header is kept; the bodies are merged
under their own namespaces.  The merge is verified locally by concatenating the
same three files and type-checking the result.
"""
import json
import os
import re

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
DEFS = os.path.join(ROOT, "Definitions")
SRC = os.path.join(DEFS, "Def_TaoFivePrimes_Theorem51Assembly.lean")
DEPS = [
    os.path.join(DEFS, "Def_TaoFivePrimes_BlockFoundation.lean"),
]
OUT = os.path.join(ROOT, "missions", "five-primes", "block-foundation",
                   "definition-assembly-payload.json")

HEADER = """import Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

set_option maxHeartbeats 800000

/-! # Type I block summation: complete reusable stack (foundation + sums + assembly)

Self-contained merge of

* the reusable foundation for Tao's Section 5 block summation
  (`rdist`, inequality (2.1), the small-`d` core (5.15)-(5.16), the block
  structure, the frozen envelope, and the Corollary 3.5 reindexing);
* the platform's divisor interface `TaoFivePrimes.theorem51Divisors` /
  `theorem51TypeI` / `theorem51Centered` / `theorem51TypeII`;
* the assembly half of `TaoFivePrimes.theorem51_typeI_block_summation`
  (coprimality transfer, double-angle transfer of (5.16), integral test,
  block partition, envelope split).

Every declaration is `sorry`-free and Mathlib-only. -/

open Finset

namespace TaoFivePrimes

/-- Positive odd divisor indices at most `UV`.  This is the platform's
`TaoFivePrimes.theorem51Divisors`, reproduced here (it is the only part of the
divisor interface the assembly needs) so that the definition compiles
standalone on the platform. -/
noncomputable def theorem51Divisors (U V : ℝ) : Finset ℕ :=
  (Icc 1 ⌊U * V⌋₊).filter (fun d => d.Coprime 2)

end TaoFivePrimes
"""

NL = r"""**The assembly half of Tao's Type I block summation: from the pointwise envelope to the two-term bound.**

This module is the second child of `TaoFivePrimes.theorem51_typeI_block_summation`. It supplies everything in the passage (5.14) → (5.17) of Tao, arXiv:1201.6656v4, Section 5.2, that is *not* the odd-restricted Vinogradov estimate itself.

**§1 — divisibility transfer.** `not_dvd_mul_of_coprime`: if $q$ is coprime to $a$ and $q \nmid d$ then $q \nmid ad$; `not_dvd_of_lt`: $0 < d < q$ implies $q \nmid d$. These feed the `¬ (q ∣ ad)` hypothesis of `rdist_d_alpha_ge`.

**§2 — the small-$d$ cosecant bound (Tao's (5.16)).** From $\|4d\alpha\|_{\mathbb R/\mathbb Z} \ge 1/(2q)$ and (2.1), $1/|\sin(2\pi d\alpha)| \le 2q$.

**§3 — the integral test.** `AntitoneOn.sum_le_integral` at the split point $x_0 = 0$ bounds $\sum_{0 \le j \le J} x/(2jq + q/2)$ above by $\int_0^J x/(2tq+q/2)\,dt$. The substitution $t \mapsto t + 1/4$ (`intervalIntegral.integral_comp_add_right`) followed by `integral_inv` evaluates this to
$$\sum_{0\le j\le J} \frac{x}{2jq+q/2} \le \frac{x}{2q}\log\frac{J+1/4}{1/4} + \frac{x}{q/2},$$
i.e. $\frac{x}{2q}\log(4J+1) + \frac{2x}{q}$. The trailing $+ 2x/q$ is exactly the $j = 0$ term that the source's displayed integral neglects — this is the same correction that, at $J = UV/(2q) - 1/4$, produces the restored $+4$ inside the node's $\log(2UV/q + 4)$.

**§4 — block combinatorics.** With `blockFinset q j = Ioc ((4jq+q)/2) ((4(j+1)q+q)/2)`:
* `mem_blockFinset_iff` — membership in doubled integer form, $4jq + q < 2d \le 4(j+1)q+q$, avoiding $\uparrow q/2$ atoms;
* `mem_blockFinset_index` — **coverage**: for $q < 2d$, $d$ lies in block $\lfloor (2d - q - 1)/(4q) \rfloor$. The naive candidate $\lfloor (2d-q)/(4q)\rfloor$ is *false* (at $q = 4$, $d = 10$ it names block $1$, whose left endpoint $20$ exceeds $10$); the $-1$ is supplied by the auxiliary `lt_div_add_one_mul`;
* `blockFinset_unique` / `blockFinset_disjoint` — a $d > q/2$ lies in at most one block;
* `biUnion_blockFinset` — **telescoping**: $\bigcup_{0 \le j \le J} \text{block}_j = \mathrm{Ioc}\,(q/2)\ ((4(J+1)q+q)/2)$, so blocks partition the range $d > q/2$ contiguously.

**§5 — the envelope split.** The node's envelope is the `min` of a $\frac{x}{d}$ term and a cosecant term. Writing `env1 x d = (1/2)(x/d)\log x + 4(\log 2)\log 2x` and `env2 α x d = 4(\log 2)(\log 2x)/|\sin(2\pi d \alpha)|`, `envelope_le_sum` shows the envelope is bounded by `env1 + env2`, and both pieces are proved nonnegative. This is what lets the two summands be summed over blocks separately.

**Formalization Note.** Everything is `sorry`-free and Mathlib-only, with the only axioms `propext`, `Classical.choice`, `Quot.sound`. The `omega` tactic treats $2d - q$ as an opaque atom, so the arithmetic facts connecting $\uparrow(2d-q)$ with $\uparrow d, \uparrow q$ are supplied as named hypotheses and the products $4 \cdot ((2d-q)/(4q)) \cdot q$ are pre-normalized by `ring` into $(c) \cdot (4q)$; without this the divisibility reasoning does not close.
"""


def strip_header(path):
    """Return everything after the last top-level `import`/`set_option` line."""
    with open(path, "r", encoding="utf-8") as fh:
        lines = fh.read().splitlines()
    start = 0
    for i, ln in enumerate(lines):
        s = ln.strip()
        if s.startswith("import ") or s.startswith("set_option ") or s == "" or s.startswith("open "):
            start = i + 1
        else:
            break
    return "\n".join(lines[start:]).strip("\n")


def merge():
    parts = [HEADER]
    for p in DEPS + [SRC]:
        parts.append(strip_header(p))
    return "\n\n".join(parts) + "\n"


def main():
    body = merge()
    payload = {
        "definition_name": "TaoFivePrimes_Theorem51Assembly",
        "definition_title": "Tao Type I block summation, full stack: foundation, divisor interface, and the block-envelope assembly",
        "definition": body,
        "natural_language_statement": NL,
        "source": (
            "Terence Tao, \"Every odd number greater than 1 is the sum of at most five primes\", "
            "Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, "
            "https://arxiv.org/abs/1201.6656, Section 5.2, the block decomposition (5.14)-(5.17), "
            "and Section 2, inequality (2.1)."
        ),
        "tags": ["analytic-number-theory", "exponential-sums", "goldbach", "number-theory"],
    }
    with open(OUT, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, ensure_ascii=False, indent=2)
    n = len(re.findall(r"^(?:lemma|theorem|noncomputable def|def) ", body, re.M))
    print("wrote", OUT, len(body), "bytes of Lean,", n, "declarations")


if __name__ == "__main__":
    main()
