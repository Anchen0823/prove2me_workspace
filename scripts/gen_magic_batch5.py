# -*- coding: utf-8 -*-
"""Batch 5: the two directions of the MacMahon parametrization (plan items 6 & 7)."""
import io
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

BECK = (
    "Beck, Cohen, Cuomo & Gribelyuk, The number of ``magic'' squares, cubes and "
    "hypercubes, Amer. Math. Monthly 110 (2003), 707--717; arXiv:math/0201013v3."
)
XIN = (
    "G. Xin, Constructing all magic squares of order three, "
    "Discrete Math. 308 (2008); arXiv:math/0610771."
)

PRE = ("import Mathlib\n"
       "import Definitions.Def_MagicSquares\n"
       "import Definitions.Def_MagicSquaresParam3\n")

MATRIX = r"""\begin{pmatrix}
a & 3e-a-c & c\\
e+c-a & e & e+a-c\\
2e-c & a+c-e & 2e-a
\end{pmatrix}"""

PROBLEMS = [
    dict(
        theorem_name="MagicSquares.magic_three_param_sufficient",
        theorem_title="The three-parameter array is a magic square of line sum 3e",
        preamble=PRE,
        formal_statement=(
            "namespace MagicSquares\n\n"
            "theorem magic_three_param_sufficient (e a c : \u2115) (h : IsParam3 e a c) :\n"
            "    IsMagic (mkMagic3 e a c) (3 * e) := by sorry\n\n"
            "end MagicSquares"
        ),
        natural_language_statement=r"""**The parametrization is sound.** Let $e,a,c$ be nonnegative integers
satisfying the admissibility inequalities

$$
e \le a+c,\qquad a+c \le 3e,\qquad a \le e+c,\qquad c \le e+a ,
$$

and let $M(a,c)$ be the array

$$
""" + MATRIX + r""" .
$$

Then $M(a,c)$ is a **magic square** of line sum $3e$: all three rows, all three
columns, and both main diagonals sum to $3e$.

The inequalities are exactly what makes the truncations in $\mathbb{N}$ harmless.
Row $0$ needs $a+c\le 3e$ so that $3e-a-c$ is not truncated; row $1$ needs
$a\le e+c$ and $c\le e+a$ for the same reason on $e+c-a$ and $e+a-c$; row $2$
needs $c\le 2e$, $a+c\ge e$ and $a\le 2e$, and the bounds $a,c\le 2e$ follow
from the hypotheses by adding $a\le e+c$ to $a+c\le 3e$ (giving $2a\le 4e$) and
symmetrically. The columns and diagonals are then pure cancellation.

Together with the companion *necessary* direction this shows that the map
$(a,c)\mapsto M(a,c)$ is a parametrization of the order-three magic squares of
line sum $3e$.

**Formalization Note** `mkMagic3` is defined over $\mathbb{N}$ with truncated
subtraction, so every line identity is proved by `omega` after discharging the
relevant non-truncation side condition. The statement is otherwise unconditional
apart from admissibility.""",
        source=BECK + " " + XIN,
    ),
    dict(
        theorem_name="MagicSquares.magic_three_param_necessary",
        theorem_title="Every order-three magic square of line sum 3e is the parametrized one",
        preamble=PRE,
        formal_statement=(
            "namespace MagicSquares\n\n"
            "theorem magic_three_param_necessary (e : \u2115) (M : Square 3 \u2115)\n"
            "    (hM : IsMagic M (3 * e)) :\n"
            "    M = mkMagic3 e (M 0 0) (M 0 2) := by sorry\n\n"
            "end MagicSquares"
        ),
        natural_language_statement=r"""**The parametrization is complete.** Let $M$ be a $3\times3$ magic square with
nonnegative integer entries and line sum $3e$. Then $M$ is *exactly* the
parametrized array built from its two top corners:

$$
M \;=\; """ + MATRIX.replace("a", "M_{00}").replace("c", "M_{02}") + r""" ,
$$

where $a=M_{00}$ and $c=M_{02}$.

The eight line identities determine the remaining seven cells uniquely. The
centre is $e$ (MacMahon's identity $3M_{11}=s$ with $s=3e$). The two diagonals
give $M_{22}=2e-M_{00}$ and $M_{20}=2e-M_{02}$; row $0$ then gives
$M_{01}=3e-M_{00}-M_{02}$; column $0$ and column $2$ give
$M_{10}=e+M_{02}-M_{00}$ and $M_{12}=e+M_{00}-M_{02}$; and column $1$ gives
$M_{21}=M_{00}+M_{02}-e$. Since $M$ is a genuine square over $\mathbb{N}$, none
of these subtractions truncates.

Consequently a $3\times3$ magic square of line sum $3e$ is determined by its two
top corners, and the pair $(M_{00},M_{02})$ satisfies precisely the
admissibility inequalities — the count of such squares is therefore the count of
admissible pairs, which is MacMahon's $2e^{2}+2e+1$.

**Formalization Note** The proof expands the eight line identities of `IsMagic`
and closes each of the nine cell equalities by `omega`; no integrality
hypothesis beyond working over $\mathbb{N}$ is needed.""",
        source=BECK + " " + XIN,
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
    path = os.path.join(ROOT, "missions", "magic-squares", "submit-problems-batch5.json")
    with io.open(path, "w", encoding="utf-8") as fh:
        json.dump(out, fh, ensure_ascii=False, indent=1)
    print("wrote", path)

    parts = []
    for p in PROBLEMS:
        parts.append(p["preamble"])
        parts.append(p["formal_statement"])
        parts.append("")
    chk = os.path.join(ROOT, "examples", "magic-squares", "statements5.lean")
    with io.open(chk, "w", encoding="utf-8") as fh:
        fh.write("\n".join(parts))
    print("wrote", chk)


if __name__ == "__main__":
    main()
