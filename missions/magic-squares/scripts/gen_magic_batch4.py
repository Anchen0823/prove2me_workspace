# -*- coding: utf-8 -*-
"""Generate and submit batch 4: the elementary structural toolbox for magic squares.

These follow the mobile plan:
  1. total sum = n * line sum
  2. transpose / vertical flip / horizontal flip preserve magic
  3. affine substitution M -> a*M + b preserves magic with line sum a*s + n*b
  5. in an order-three magic square, opposite cells sum to 2 * centre
"""
import io
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))

BECK = (
    "Beck, Cohen, Cuomo & Gribelyuk, The number of ``magic'' squares, cubes and "
    "hypercubes, Amer. Math. Monthly 110 (2003), 707--717; arXiv:math/0201013v3."
)

PRE_BASE = "import Mathlib\nimport Definitions.Def_MagicSquares\n"
PRE_TRA = "import Mathlib\nimport Definitions.Def_MagicSquares\nimport Definitions.Def_MagicSquaresTransforms\n"

PROBLEMS = [
    dict(
        theorem_name="MagicSquares.total_sum_eq_n_line_sum",
        theorem_title="Total sum of a semi-magic square is n times the line sum",
        preamble=PRE_BASE,
        formal_statement=(
            "namespace MagicSquares\n\n"
            "theorem total_sum_eq_n_line_sum {n : \u2115} {\u03b1 : Type*} [AddCommMonoid \u03b1]\n"
            "    (M : Square n \u03b1) (s : \u03b1) (hM : IsSemiMagic M s) :\n"
            "    totalSum M = n \u2022 s := by sorry\n\n"
            "end MagicSquares"
        ),
        natural_language_statement=r"""**Row-sum aggregation.** Let $A$ be an $n\times n$ array over an additive
commutative monoid, and suppose every row sums to the same value $S$ (a
*semi-magic square* of line sum $S$). Then the sum of **all** $n^{2}$ entries is

$$
\sum_{i}\sum_{j} A_{ij} \;=\; n\,S .
$$

Indeed the total is the sum of the $n$ row sums, each of which equals $S$. This
is the first structural identity of the theory: it is what converts the
*row* condition into a global constraint, and it is the reason the magic
constant of a normal magic square of order $n$ must be $n(n^{2}+1)/2$ — the
entries are $1,\dots,n^{2}$, whose total is $n^{2}(n^{2}+1)/2$, and dividing by
$n$ gives the line sum.

**Formalization Note** Entries live in an arbitrary `AddCommMonoid`, so the
statement reads $n\bullet S$ (`nsmul`) rather than $n\cdot S$; over $\mathbb{N}$
or a semiring the two coincide. Only the row half of `IsSemiMagic` is used.""",
        source=BECK,
    ),
    dict(
        theorem_name="MagicSquares.transpose_preserves_magic",
        theorem_title="Transposing a magic square preserves magicness",
        preamble=PRE_TRA,
        formal_statement=(
            "namespace MagicSquares\n\n"
            "theorem transpose_preserves_magic {n : \u2115} {\u03b1 : Type*} [AddCommMonoid \u03b1]\n"
            "    (M : Square n \u03b1) (s : \u03b1) (hM : IsMagic M s) :\n"
            "    IsMagic (transpose M) s := by sorry\n\n"
            "end MagicSquares"
        ),
        natural_language_statement=r"""**Transposition.** If $A$ is a magic square of line sum $S$, so is its
transpose $A^{\mathsf T}$, with the same line sum.

The square is a symmetry of the $n\times n$ grid, so it permutes the lines:
rows of $A^{\mathsf T}$ are the columns of $A$ and vice versa, while each main
diagonal is fixed. Hence every line of $A^{\mathsf T}$ is a line of $A$ and
still sums to $S$, and the same holds verbatim for panmagic (pandiagonal)
squares, whose broken diagonals are also carried to broken diagonals.

**Formalization Note** `transpose` is the entrywise flip $(i,j)\mapsto(j,i)$
from `Definitions.Def_MagicSquaresTransforms`. The four line sums are tracked by
`rowSum_transpose`, `colSum_transpose`, `diagSum_transpose` and
`antiDiagSum_transpose`; the anti-diagonal case uses that $i\mapsto n-1-i$ is a
bijection of $\mathrm{Fin}\,n$, so reindexing the sum is legitimate.""",
        source=BECK,
    ),
    dict(
        theorem_name="MagicSquares.flipVertical_preserves_magic",
        theorem_title="Vertical flip preserves magicness",
        preamble=PRE_TRA,
        formal_statement=(
            "namespace MagicSquares\n\n"
            "theorem flipVertical_preserves_magic {n : \u2115} {\u03b1 : Type*} [AddCommMonoid \u03b1]\n"
            "    (M : Square n \u03b1) (s : \u03b1) (hM : IsMagic M s) :\n"
            "    IsMagic (flipVertical M) s := by sorry\n\n"
            "end MagicSquares"
        ),
        natural_language_statement=r"""**Vertical reflection.** Reversing the order of the rows of a magic square
again gives a magic square, with the same line sum.

The reflection $(i,j)\mapsto(n-1-i,\,j)$ sends rows to rows and columns to
columns, so every row and column of the reflected array is a row or column of the
original and sums to $S$. The two main diagonals are **interchanged**: the
descending diagonal of the reflected square is the ascending diagonal of the
original, and conversely. Since a magic square requires both diagonals to sum to
$S$, the reflected array satisfies all the conditions.

Together with the horizontal flip and the transpose, this generates the full
dihedral symmetry group of order $8$ of the square, under which the set of magic
squares of a fixed line sum is closed — the fact that makes "up to symmetry"
counts meaningful.

**Formalization Note** `flipVertical` reverses the row index via `Fin.rev`.
Column sums are invariant because $i\mapsto n-1-i$ permutes $\mathrm{Fin}\,n$, and
the diagonal swap is proved by the same reindexing.""",
        source=BECK,
    ),
    dict(
        theorem_name="MagicSquares.flipHorizontal_preserves_magic",
        theorem_title="Horizontal flip preserves magicness",
        preamble=PRE_TRA,
        formal_statement=(
            "namespace MagicSquares\n\n"
            "theorem flipHorizontal_preserves_magic {n : \u2115} {\u03b1 : Type*} [AddCommMonoid \u03b1]\n"
            "    (M : Square n \u03b1) (s : \u03b1) (hM : IsMagic M s) :\n"
            "    IsMagic (flipHorizontal M) s := by sorry\n\n"
            "end MagicSquares"
        ),
        natural_language_statement=r"""**Horizontal reflection.** Reversing the order of the columns of a magic square
again gives a magic square, with the same line sum.

This is the mirror image of the vertical flip: $(i,j)\mapsto(i,\,n-1-j)$ sends
columns to columns and rows to rows, and interchanges the two main diagonals. All
lines therefore still sum to $S$.

**Formalization Note** `flipHorizontal` reverses the column index via `Fin.rev`.
Row sums are invariant by reindexing; the two diagonals are swapped.""",
        source=BECK,
    ),
    dict(
        theorem_name="MagicSquares.affine_preserves_magic",
        theorem_title="Affine substitution preserves the magic property",
        preamble=PRE_TRA,
        formal_statement=(
            "namespace MagicSquares\n\n"
            "theorem affine_preserves_magic {n : \u2115} {\u03b1 : Type*} [Semiring \u03b1]\n"
            "    (M : Square n \u03b1) (s a b : \u03b1) (hM : IsMagic M s) :\n"
            "    IsMagic (affine a b M) (a * s + n \u2022 b) := by sorry\n\n"
            "end MagicSquares"
        ),
        natural_language_statement=r"""**Affine substitution.** Let $A$ be a magic square of order $n$ with line sum
$S$, and let $a,b$ be scalars. The array $A'$ with entries

$$
A'_{ij} \;=\; a\,A_{ij} + b
$$

is again magic, with line sum

$$
S' \;=\; aS + nb .
$$

Each line has exactly $n$ entries, so its sum becomes $aS+nb$; this applies to
rows, columns and both main diagonals alike. The shift by $b$ contributes $nb$
because it is added $n$ times along the line.

Two consequences drive the enumerative theory. Taking $a=1$ shows that the
counting function depends only on the line sum up to translation, and taking
$a=-1,\ b=n^{2}+1$ over $\mathbb{Z}$ gives the classical *complement*
$A\mapsto n^{2}+1-A$, which sends a normal magic square of order $n$ to another
one with line sum $n(n^{2}+1)-S$.

**Formalization Note** `affine a b M` is the entrywise map from
`Definitions.Def_MagicSquaresTransforms`. The ring law is used only to distribute
$a$ over a finite sum and to collapse $\sum_{j} b$ to $n\bullet b$.""",
        source=BECK,
    ),
    dict(
        theorem_name="MagicSquares.order_three_opposite_sum_eq_twice_center",
        theorem_title="In an order-three magic square, opposite cells sum to twice the centre",
        preamble=PRE_BASE,
        formal_statement=(
            "namespace MagicSquares\n\n"
            "theorem order_three_opposite_sum_eq_twice_center\n"
            "    (M : Square 3 \u2115) (s : \u2115) (hM : IsMagic M s) (i j : Fin 3) :\n"
            "    M i j + M (Fin.rev i) (Fin.rev j) = 2 * M 1 1 := by sorry\n\n"
            "end MagicSquares"
        ),
        natural_language_statement=r"""**Opposite cells in an order-three magic square.** Let $A$ be a $3\times3$
magic square with line sum $S$. Then for **every** pair of centrally opposite
cells,

$$
A_{ij} + A_{2-i,\,2-j} \;=\; 2\,A_{11} .
$$

Equivalently, an order-three magic square is automatically *associative* with
complement constant $2A_{11}$. Since MacMahon's identity gives $S = 3A_{11}$,
each such pair sums to $\tfrac23 S$, and in particular the square is determined
by its centre: every opposite pair is pinned to twice it.

The four pairs are $(1,1)$–$(3,3)$ and $(1,3)$–$(3,1)$ (the two diagonals) and
$(1,2)$–$(3,2)$, $(2,1)$–$(2,3)$ (the middle column and middle row); the fifth
"pair" is the centre with itself, which is trivial. This is the structural fact
behind the classical parametrisation of $3\times3$ magic squares by two corner
entries: once $A_{11}$ and one corner are chosen, all remaining cells follow.

**Formalization Note** Cells are indexed by `Fin 3` and `Fin.rev` is the
reversal $i\mapsto 2-i$, so $(i,j)$ and $(\mathrm{rev}\,i,\mathrm{rev}\,j)$ are
the centrally opposite pair. The proof expands the nine line identities and
finishes by linear arithmetic; no integrality hypothesis beyond $\mathbb{N}$ is
needed.""",
        source=BECK,
    ),
]


def main():
    out = {
        "problems": [
            {
                "theorem_name": p["theorem_name"],
                "theorem_title": p["theorem_title"],
                "formal_statement": p["formal_statement"],
                "natural_language_statement": p["natural_language_statement"],
                "preamble": p["preamble"],
                "source": p["source"],
                "tags": ["combinatorics", "magic-squares"],
            }
            for p in PROBLEMS
        ]
    }
    path = os.path.join(ROOT, "missions", "magic-squares", "submit-problems-batch4.json")
    with io.open(path, "w", encoding="utf-8") as fh:
        json.dump(out, fh, ensure_ascii=False, indent=1)
    print("wrote", path)

    # local statement check
    parts = []
    for p in PROBLEMS:
        parts.append(p["preamble"])
        parts.append(p["formal_statement"])
        parts.append("")
    chk = os.path.join(ROOT, "examples", "magic-squares", "statements4.lean")
    with io.open(chk, "w", encoding="utf-8") as fh:
        fh.write("\n".join(parts))
    print("wrote", chk)


if __name__ == "__main__":
    main()
