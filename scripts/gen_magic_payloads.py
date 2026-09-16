#!/usr/bin/env python
"""Build the JSON payloads for the magic-squares foundation on Prove2me.

Writes:
  missions/magic-squares/submit-definition.json
  missions/magic-squares/submit-problems-batch1.json
"""
import io
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MISSION = os.path.join(ROOT, "missions", "magic-squares")

DEF_SRC = os.path.join(ROOT, "Definitions", "Def_MagicSquares.lean")

BECK = (
    "Beck, Cohen, Cuomo & Gribelyuk, The number of ``magic'' squares, cubes and "
    "hypercubes, Amer. Math. Monthly 110 (2003), 707-717; arXiv:math/0201013v3"
)

DEFINITION_NL = r"""Core vocabulary for the theory of magic squares: an $n \times n$ array
(`Square`), its row, column, main-diagonal, anti-diagonal and broken-diagonal sums, and the
standard predicates used in the literature.

A **semi-magic square** of line sum $s$ has every row and every column summing to $s$; it is
**magic** if both main diagonals also sum to $s$, and **panmagic** (pandiagonal) if every
broken diagonal in both directions does. A square is **associative** with constant $c$ when
centrally opposite cells sum to $c$, and **compact** with constant $c$ when every
$2 \times 2$ block -- including the ones that wrap around the edges -- sums to $c$.

A square is **normal** of order $n$ when its entries are exactly the integers
$1, \dots, n^{2}$, each occurring once. Then `magicConstant n` $= n(n^{2}+1)/2$ is the common
line sum, and `complement` is the involution $M \mapsto n^{2}+1-M$.

Finally the module fixes the four classical counting functions: $H_{n}(t)$ (semi-magic),
$M_{n}(t)$ (magic), $P_{n}(t)$ (panmagic) and $S_{n}(t)$ (symmetric magic), each counting
squares of order $n$ with nonnegative integer entries and line sum $t$. Since every entry of
such a square is at most $t$, searching over arrays with entries in $\{0,\dots,t\}$ loses
nothing.

**Formalization Note** Entries are indexed by `Fin n`, so broken diagonals are obtained by
addition modulo $n$ and the anti-diagonal by `Fin.rev`. The counting functions are
cardinalities of finsets of arrays over `Fin (t+1)`.
"""

PROBLEMS = [
    dict(
        theorem_name="MagicSquares.magic_constant_of_normal",
        theorem_title="Magic constant of a normal magic square",
        formal_statement=(
            "namespace MagicSquares\n\n"
            "theorem magic_constant_of_normal (n : ℕ) (M : Square n ℕ) (s : ℕ)\n"
            "    (hN : IsNormal M) (hM : IsMagic M s) :\n"
            "    2 * s = n * (n ^ 2 + 1) := by sorry\n\n"
            "end MagicSquares"
        ),
        natural_language_statement=r"""Every normal magic square has the magic constant
$n(n^{2}+1)/2$.

Let $M$ be an $n \times n$ array whose entries are exactly the integers $1,2,\dots,n^{2}$,
each used once, and suppose every row, every column and both main diagonals of $M$ sum to the
same number $s$. Then

$$
2s = n\,(n^{2}+1).
$$

Equivalently $s = n(n^{2}+1)/2$, the classical magic constant: it is $\tfrac{1}{n}$ of the sum
$1+2+\cdots+n^{2} = n^{2}(n^{2}+1)/2$ of all entries.

**Formalization Note** The division by $2$ is avoided by multiplying through, so the statement
is an identity in $\mathbb{N}$. Normality is the conjunction of the entry bounds
$1 \le M_{ij} \le n^{2}$ with injectivity of the index-to-entry map.""",
        source=(
            "Standard folklore; stated e.g. in Weisstein, MathWorld, \"Magic Square\", "
            "eq. for the magic constant of a normal magic square."
        ),
    ),
    dict(
        theorem_name="MagicSquares.center_of_order_three",
        theorem_title="The centre of a 3x3 magic square is one third of the line sum",
        formal_statement=(
            "namespace MagicSquares\n\n"
            "theorem center_of_order_three (M : Square 3 ℕ) (s : ℕ)\n"
            "    (hM : IsMagic M s) :\n"
            "    3 * M 1 1 = s := by sorry\n\n"
            "end MagicSquares"
        ),
        natural_language_statement=r"""In a $3 \times 3$ magic square the centre entry is
exactly one third of the magic constant.

Let $M$ be a $3 \times 3$ array of natural numbers whose three rows, three columns and two
main diagonals all sum to the same number $s$. Then

$$
3 \cdot M_{1,1} = s ,
$$

where $M_{1,1}$ is the central entry (indices are `Fin 3`, so the centre is the index $1$).

The proof is the classical one: add the middle row, the middle column and the two diagonals.
The centre is counted four times and every other cell exactly once, so the total is
$3s + 3M_{1,1}$; but it is also $4s$, whence $s = 3M_{1,1}$.

**Formalization Note** Everything stays in $\mathbb{N}$, so no divisibility hypothesis is
needed: the identity itself forces $3 \mid s$.""",
        source=(
            "Classical (Lo Shu); see Beck, Cohen, Cuomo & Gribelyuk, arXiv:math/0201013v3, "
            "Section 2, where the $3\\times3$ magic square is parametrised by the centre "
            "entry $e$ with line sum $3e$."
        ),
    ),
    dict(
        theorem_name="MagicSquares.normal_order_two_none",
        theorem_title="There is no normal magic square of order 2",
        formal_statement=(
            "namespace MagicSquares\n\n"
            "theorem normal_order_two_none :\n"
            "    ¬ ∃ (M : Square 2 ℕ) (s : ℕ), IsNormal M ∧ IsMagic M s := by sorry\n\n"
            "end MagicSquares"
        ),
        natural_language_statement=r"""No $2 \times 2$ array can have the four distinct
entries $1,2,3,4$ and be magic.

Suppose $M = \begin{pmatrix} a & b \\ c & d \end{pmatrix}$ has all rows, columns and both
diagonals summing to $s$. Comparing the first row $a+b=s$ with the main diagonal $a+d=s$ gives
$b=d$, contradicting the requirement that the four entries be distinct. Hence no **normal**
magic square of order $2$ exists.

This is the $n=2$ instance of the general fact that normal magic squares exist for every order
$n \ge 1$ except $n = 2$.

**Formalization Note** `IsNormal` supplies injectivity of the index-to-entry map, and the two
cells $(0,1)$ and $(1,1)$ are distinct, so the equality $b=d$ is immediately contradictory.""",
        source=(
            "Classical; consistent with Beck, Cohen, Cuomo & Gribelyuk, "
            "arXiv:math/0201013v3, Section 2, where $M_{2}(t)=1$ for even $t$ and $0$ "
            "otherwise (i.e. every order-2 magic square has four equal entries)."
        ),
    ),
    dict(
        theorem_name="MagicSquares.magic_count_three_divisible",
        theorem_title="MacMahon's count of 3x3 magic squares with line sum a multiple of 3",
        formal_statement=(
            "namespace MagicSquares\n\n"
            "theorem magic_count_three_divisible (e : ℕ) :\n"
            "    magicCount 3 (3 * e) = 2 * e ^ 2 + 2 * e + 1 := by sorry\n\n"
            "end MagicSquares"
        ),
        natural_language_statement=r"""MacMahon's 1915 count of $3 \times 3$ magic squares
whose line sum is a multiple of $3$.

Write $M_{3}(t)$ for the number of $3 \times 3$ arrays of nonnegative integers whose three
rows, three columns and two main diagonals all sum to $t$ (entries need not be distinct). Then
$M_{3}(t)$ vanishes unless $3 \mid t$, and for $t = 3e$,

$$
M_{3}(3e) = 2e^{2} + 2e + 1 ,
$$

which is the integral form of $\tfrac{2}{9}t^{2} + \tfrac{2}{3}t + 1$.

The companion statement `MagicSquares.magic_count_three_otherwise` records the vanishing when
$3 \nmid t$; together they give the complete counting function.

**Formalization Note** `magicCount n t` counts arrays with entries in `Fin (t+1)` satisfying
the magic identities after coercion to `ℕ`. This is lossless because every entry of a
nonnegative magic square with line sum $t$ is at most $t$.""",
        source=BECK + ", Section 2, MacMahon's formula for $M_{3}(t)$ (1915).",
    ),
    dict(
        theorem_name="MagicSquares.magic_count_three_otherwise",
        theorem_title="No 3x3 magic square has a line sum coprime to 3",
        formal_statement=(
            "namespace MagicSquares\n\n"
            "theorem magic_count_three_otherwise (t : ℕ) (ht : ¬ 3 ∣ t) :\n"
            "    magicCount 3 t = 0 := by sorry\n\n"
            "end MagicSquares"
        ),
        natural_language_statement=r"""If $t$ is not divisible by $3$, there is no
$3 \times 3$ magic square with line sum $t$.

Write $M_{3}(t)$ for the number of $3 \times 3$ arrays of nonnegative integers whose three
rows, three columns and two main diagonals all sum to $t$. Then

$$
3 \nmid t \;\Longrightarrow\; M_{3}(t) = 0 .
$$

This is an immediate consequence of the fact that the centre entry satisfies
$3M_{1,1} = t$; see `MagicSquares.center_of_order_three`. Together with
`MagicSquares.magic_count_three_divisible` this determines $M_{3}$ completely.""",
        source=BECK + ", Section 2, MacMahon's formula for $M_{3}(t)$ (1915).",
    ),
    dict(
        theorem_name="MagicSquares.semi_magic_count_three",
        theorem_title="MacMahon's count of 3x3 semi-magic squares by line sum",
        formal_statement=(
            "namespace MagicSquares\n\n"
            "theorem semi_magic_count_three (t : ℕ) :\n"
            "    semiMagicCount 3 t = 3 * ((t + 3).choose 4) + ((t + 2).choose 2) := by sorry\n\n"
            "end MagicSquares"
        ),
        natural_language_statement=r"""MacMahon's 1915 formula for the number of
$3 \times 3$ semi-magic squares of a given line sum.

Write $H_{3}(t)$ for the number of $3 \times 3$ arrays of nonnegative integers whose three rows
and three columns all sum to $t$ (the diagonals are unconstrained, and entries need not be
distinct). Then

$$
H_{3}(t) = 3\binom{t+3}{4} + \binom{t+2}{2}.
$$

Unlike the magic count $M_{3}(t)$, this is an honest polynomial in $t$ of degree
$(3-1)^{2} = 4$: Ehrhart and Stanley proved that $H_{n}(t)$ is a polynomial of degree
$(n-1)^{2}$ for every $n$, satisfying the reciprocity law $H_{n}(-n-t) = (-1)^{n-1}H_{n}(t)$.

**Formalization Note** `semiMagicCount n t` counts arrays with entries in `Fin (t+1)` whose
row and column sums are $t$ after coercion to `ℕ`; the bound on entries makes the finite
search space exact.""",
        source=BECK + ", Section 2, Theorem 1 (MacMahon's formula for $H_{3}(t)$).",
    ),
]


def main():
    os.makedirs(MISSION, exist_ok=True)

    with io.open(DEF_SRC, encoding="utf-8") as fh:
        src = fh.read()

    def_payload = {
        "definition_name": "MagicSquares",
        "definition_title": "Magic squares: core definitions and counting functions",
        "definition": src,
        "natural_language_statement": DEFINITION_NL,
        "source": BECK + ", Section 1 (definitions) and Section 2 (Theorem 1).",
        "tags": ["combinatorics", "magic-squares", "enumerative-combinatorics"],
    }
    with io.open(os.path.join(MISSION, "submit-definition.json"), "w", encoding="utf-8") as fh:
        json.dump(def_payload, fh, ensure_ascii=False, indent=1)

    prob_payload = {
        "problems": [
            {
                "theorem_name": p["theorem_name"],
                "theorem_title": p["theorem_title"],
                "formal_statement": p["formal_statement"],
                "natural_language_statement": p["natural_language_statement"],
                "preamble": "import Mathlib\nimport Definitions.Def_MagicSquares\nopen MagicSquares",
                "source": p["source"],
                "tags": ["combinatorics", "magic-squares"],
            }
            for p in PROBLEMS
        ]
    }
    with io.open(
        os.path.join(MISSION, "submit-problems-batch1.json"), "w", encoding="utf-8"
    ) as fh:
        json.dump(prob_payload, fh, ensure_ascii=False, indent=1)

    print("wrote", len(PROBLEMS), "problems + 1 definition payload")


if __name__ == "__main__":
    main()
