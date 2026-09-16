#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""Generate Prove2me submission payloads for the magic-squares mission, batch 2:
structural corollaries for normal 3x3 magic squares."""
import io
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "missions", "magic-squares", "submit-problems-batch2.json")

PREAMBLE = "import Mathlib\nimport Definitions.Def_MagicSquares\nopen MagicSquares"

BCCG = ("Beck, Cohen, Cuomo & Gribelyuk, The number of ``magic'' squares, cubes and "
        "hypercubes, Amer. Math. Monthly 110 (2003), 707--717; arXiv:math/0201013v3.")

PROBLEMS = [
    dict(
        theorem_name="MagicSquares.normal_order_three_constant",
        theorem_title="The magic constant of a normal 3x3 magic square is 15",
        formal_statement=(
            "namespace MagicSquares\n\n"
            "theorem normal_order_three_constant (M : Square 3 \u2115) (s : \u2115)\n"
            "    (hN : IsNormal M) (hM : IsMagic M s) :\n"
            "    s = 15 := by sorry\n\n"
            "end MagicSquares"
        ),
        natural_language_statement=r"""Every normal $3 \times 3$ magic square has line sum $15$.

A **normal** magic square of order $3$ has entries exactly $1, 2, \dots, 9$, each used once.
Its magic constant is therefore
$$\frac{1}{3}\,(1 + 2 + \cdots + 9) = \frac{45}{3} = 15 .$$

This is the $n = 3$ instance of the general magic-constant identity
$2s = n(n^{2}+1)$, which here reads $2s = 3 \cdot 10 = 30$.

**Formalization Note** The statement avoids division: with the hypothesis
`IsNormal M` and `IsMagic M s` the general identity gives `2 * s = 30`, and `s = 15`
follows by linear arithmetic over $\mathbb{N}$.""",
        source="Standard folklore on the Lo Shu square; the general identity is the "
               "magic-constant formula for normal magic squares.",
    ),
    dict(
        theorem_name="MagicSquares.normal_order_three_center_five",
        theorem_title="The centre of a normal 3x3 magic square is 5",
        formal_statement=(
            "namespace MagicSquares\n\n"
            "theorem normal_order_three_center_five (M : Square 3 \u2115) (s : \u2115)\n"
            "    (hN : IsNormal M) (hM : IsMagic M s) :\n"
            "    M 1 1 = 5 := by sorry\n\n"
            "end MagicSquares"
        ),
        natural_language_statement=r"""The centre cell of every normal $3 \times 3$ magic square is $5$.

In any $3 \times 3$ magic square of line sum $s$ the centre entry is $s/3$
(MacMahon): adding the middle row, the middle column and the two diagonals counts
the centre four times and every other cell once, giving
$\mathrm{total} + 3\,M_{11} = 4s$ while $\mathrm{total} = 3s$. For a *normal*
square $s = 15$, so $M_{11} = 5$.

**Formalization Note** This is an immediate consequence of the two children
`MagicSquares.normal_order_three_constant` ($s = 15$) and
`MagicSquares.center_of_order_three` ($3\,M_{11} = s$); the natural-number
arithmetic is discharged by `omega`.""",
        source="MacMahon (1915) for the centre identity; normality fixes $s = 15$.",
    ),
    dict(
        theorem_name="MagicSquares.normal_order_three_associative",
        theorem_title="A normal 3x3 magic square is associative with constant 10",
        formal_statement=(
            "namespace MagicSquares\n\n"
            "theorem normal_order_three_associative (M : Square 3 \u2115) (s : \u2115)\n"
            "    (hN : IsNormal M) (hM : IsMagic M s) :\n"
            "    IsAssociative M 10 := by sorry\n\n"
            "end MagicSquares"
        ),
        natural_language_statement=r"""Every normal $3 \times 3$ magic square is **associative**
(also called *regular* or *symmetric through the centre*) with complement constant $10$:
any two centrally opposite cells add up to $10$,
$$M_{ij} + M_{2-i,\,2-j} = 10 \qquad \text{for all } 0 \le i, j \le 2 .$$

Indeed the centre is $5$, and each opposite pair lies together with the centre on a
row, a column, or one of the two diagonals, all of which sum to $15$; hence each pair
sums to $15 - 5 = 10$.

The pair $\{M_{11}, M_{11}\}$ is covered too, as $5 + 5 = 10$.

**Formalization Note** `IsAssociative M c` is
`\forall i j, M i j + M (Fin.rev i) (Fin.rev j) = c`, and `Fin.rev` is the
reversal $i \mapsto 2-i$ on `Fin 3`. The proof splits the nine index pairs with
`fin_cases` and closes each by `omega` from the row/column/diagonal identities and
`s = 15`.""",
        source="Classical Lo Shu structure theory; see e.g. the associative-square "
               "discussion in " + BCCG,
    ),
    dict(
        theorem_name="MagicSquares.panmagic_is_magic",
        theorem_title="Every panmagic square is magic",
        formal_statement=(
            "namespace MagicSquares\n\n"
            "theorem panmagic_is_magic {n : \u2115} [NeZero n]\n"
            "    (M : Square n \u2115) (s : \u2115) (hP : IsPanMagic M s) :\n"
            "    IsMagic M s := by sorry\n\n"
            "end MagicSquares"
        ),
        natural_language_statement=r"""A **panmagic** (pandiagonal) square is in particular a magic square.

By definition `IsPanMagic M s` requires every row and every column to sum to $s$
(the semi-magic condition) and, in addition, *every* broken diagonal in both
directions to sum to $s$. The two main diagonals are the broken diagonals of
offset $0$, so both main diagonal sums equal $s$, which is exactly the extra
content of `IsMagic M s` over `IsSemiMagic M s`.

**Formalization Note** `brokenDiagSum M k` is $\sum_i M_{i,\, i+k}$ with the column
index read modulo $n$, so `brokenDiagSum M 0 = diagSum M`. For the anti-diagonal one
uses `brokenAntiDiagSum M 0`, i.e. $\sum_i M_{i,\, n-1-i}$, which is
`antiDiagSum M`. Only $n \neq 0$ is needed so that `Fin n` carries the additive
structure used to speak of offsets.""",
        source=BCCG + ", Section 1 (definitions of $P_n$ versus $M_n$).",
    ),
]


def main():
    payload = {"problems": []}
    for p in PROBLEMS:
        d = dict(p)
        d["preamble"] = PREAMBLE
        d["tags"] = ["combinatorics", "magic-squares"]
        payload["problems"].append(d)
    with io.open(OUT, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, ensure_ascii=False, indent=1)
    print("wrote", OUT, len(payload["problems"]), "problems")


if __name__ == "__main__":
    main()
