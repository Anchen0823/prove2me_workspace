#!/usr/bin/env python
"""Assemble `Definitions.Def_TaoFivePrimes_Theorem51Assembly` (Child 2).

The parent node `TaoFivePrimes.theorem51_typeI_block_summation` needs the
*assembly* half: from the pointwise envelope on the odd divisors to the two-term
bound.  That half is developed in `examples/five-primes/Theorem51Assembly.lean`
and, because `examples/` is not on the Lean search path, must be copied into
`Definitions/` so `lake build` sees it.

The module imports the published foundation
(`Definitions.Def_TaoFivePrimes_BlockFoundation`, which already contains the
Cor 3.5 reindexing) and the divisor interface
(`Definitions.Def_TaoFivePrimes_Theorem51Sums`).

The script rewrites the example file's import header into the library-module
header and wraps the body in the same namespace.
"""
import os
import re

ROOT = os.path.dirname(  # missions/five-primes/block-foundation -> repo root
    os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
EX = os.path.join(ROOT, "examples", "five-primes")
OUT = os.path.join(ROOT, "Definitions", "Def_TaoFivePrimes_Theorem51Assembly.lean")
SRC = os.path.join(EX, "Theorem51Assembly.lean")

HEADER = """import Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_BlockFoundation
import Definitions.Def_TaoFivePrimes_Theorem51Sums

set_option maxHeartbeats 800000

/-! # Type I block summation: the assembly (Child 2)

Tao, arXiv:1201.6656v4, Section 5.2, the passage from (5.14) to (5.17).

This module is the second child of `TaoFivePrimes.theorem51_typeI_block_summation`.
It combines

* the reusable foundation `Definitions.Def_TaoFivePrimes_BlockFoundation`
  (`rdist`, inequality (2.1), the small-`d` core (5.15)-(5.16), the block
  structure, the frozen envelope, and the Corollary 3.5 reindexing), with
* the platform's divisor interface `TaoFivePrimes.theorem51Divisors`,

to bound the whole envelope sum.  Every step of Tao's own split is a separate
lemma; see the per-section comments below.

All declarations are `sorry`-free and Mathlib-only. -/

open Finset

namespace TaoFivePrimesAssembly
"""

FOOTER = "\nend TaoFivePrimesAssembly\n"


def body_lines(path):
    """Lines strictly between the first `namespace` and last `end`."""
    with open(path, "r", encoding="utf-8") as fh:
        lines = fh.read().splitlines()
    start = end = None
    for i, ln in enumerate(lines):
        if start is None and ln.startswith("namespace "):
            start = i + 1
        if ln.rstrip() == "end TaoFivePrimesAssembly":
            end = i
    assert start is not None and end is not None, path
    return lines[start:end]


def main():
    text = HEADER + "\n".join(body_lines(SRC)).rstrip() + "\n" + FOOTER
    with open(OUT, "w", encoding="utf-8") as fh:
        fh.write(text)
    n = len(re.findall(r"^(?:lemma|theorem|noncomputable def|def) ", text, re.M))
    print("wrote", OUT)
    print("declarations:", n, "| lines:", text.count(chr(10)),
          "| sorries:", text.count("sorry"))


if __name__ == "__main__":
    main()
