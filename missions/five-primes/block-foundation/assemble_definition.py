#!/usr/bin/env python
"""Assemble the single `Definitions.Def_TaoFivePrimes_BlockFoundation` module.

The platform definition `TaoFivePrimes_BlockFoundation` (id
8bca80f4-cd0c-4f05-8144-421e9d0c905e) is the foundation section.  The
block partition and the frozen-envelope lemmas are the next layer; they
must live in the same module so `lake build` sees them, and so a single
`/submit-definition` can carry the whole reusable interface.

This script concatenates:

  examples/five-primes/Theorem51BlockFoundation.lean   (foundation, §1-5)
  examples/five-primes/Theorem51BlockPartition.lean    (block structure, §6-7)
  examples/five-primes/Theorem51BlockEnvelope.lean     (frozen envelope, §8)
  examples/five-primes/Theorem51Cor35.lean             (Cor 3.5 reindexing, §9-12)
  examples/five-primes/Theorem51SmallD.lean            (cosecant bound, §13)

into `Definitions/Def_TaoFivePrimes_BlockFoundation.lean`, keeping one
`namespace TaoFivePrimesBlock` and one `import` header.

Pass `--with-cor35` to include the Corollary 3.5 layer (default: included).
"""
import os
import re

ROOT = os.path.dirname(  # missions/five-primes/block-foundation -> repo root
    os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
EX = os.path.join(ROOT, "examples", "five-primes")
OUT = os.path.join(ROOT, "Definitions", "Def_TaoFivePrimes_BlockFoundation.lean")

HEADER = """import Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

set_option maxHeartbeats 800000

/-! # Type I block summation: reusable foundation, block structure, envelope

Reusable interface for the Prove2Me node
`TaoFivePrimes.theorem51_typeI_block_summation`, following Tao,
arXiv:1201.6656v4, Section 5, (5.14) → (5.17), and Section 2 (2.1).

Three layers, all `sorry`-free and Mathlib-only:
* **§1-5 foundation** — the distance to the nearest integer `rdist`, its
  triangle inequality, inequality (2.1), and the small-`d` core of (5.15)
  (`1/|sin (2πdα)| ≤ 2q` for `2d ≤ q`);
* **§6-7 block structure** — the block endpoints `2jq + q/2` and
  `2(j+1)q + q/2`, the bridge between the doubled integer spacing and the
  real block interval;
* **§8 frozen envelope** — the per-block domination of the pointwise
  envelope by its value frozen at the left endpoint;
* **§9-12 Corollary 3.5** — the floor helper lemmas, the index-set identity
  `2m+1 ∈ (x,y] ↔ m ∈ ((x-1)/2, (y-1)/2]`, the reindexing of the
  odd min-sum onto the full min-sum with parameter `2α` and phase
  `π α + θ`, and the resulting reduction of Corollary 3.5 to Lemma 3.4.

Design notes for this environment:

* no `conv`: rewriting under `abs`/`Real.sin` via `conv_rhs` exhausts the
  heartbeat budget.  Every step is an equality of *arguments* applied by
  `rw`;
* `linarith` cannot see through `Int.fract`/`Int.floor` casts, so each such
  bridge is a separate real-valued lemma;
* `linarith`/`nlinarith` treat `↑q / 2` as an opaque atom.  Endpoint
  statements are therefore *stated* in doubled integer form and halved
  once, after a `ring` normalization, by `div_lt_iff₀` / `le_div_iff₀`. -/

open Finset

namespace TaoFivePrimesBlock
"""

FOOTER = "\nend TaoFivePrimesBlock\n"


def body_lines(path):
    """Return the lines strictly between the first `namespace` and last `end`."""
    with open(path, "r", encoding="utf-8") as fh:
        lines = fh.read().splitlines()
    start = None
    end = None
    for i, ln in enumerate(lines):
        if start is None and ln.startswith("namespace "):
            start = i + 1
        if ln.rstrip() == "end TaoFivePrimesBlock":
            end = i
    assert start is not None and end is not None, path
    return lines[start:end]


def main():
    parts = [
        body_lines(os.path.join(EX, "Theorem51BlockFoundation.lean")),
        body_lines(os.path.join(EX, "Theorem51BlockPartition.lean")),
        body_lines(os.path.join(EX, "Theorem51BlockEnvelope.lean")),
        body_lines(os.path.join(EX, "Theorem51Cor35.lean")),
        body_lines(os.path.join(EX, "Theorem51SmallD.lean")),
    ]
    text = HEADER
    for part in parts:
        text += "\n".join(part).rstrip() + "\n"
    text += FOOTER
    with open(OUT, "w", encoding="utf-8") as fh:
        fh.write(text)
    n = len(re.findall(r"^(?:lemma|theorem|noncomputable def|def) ", text, re.M))
    print("wrote", OUT)
    print("declarations:", n, "| lines:", text.count(chr(10)), "| sorries:", text.count("sorry"))


if __name__ == "__main__":
    main()
