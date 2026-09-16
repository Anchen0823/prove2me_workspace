#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""Publish Def_MagicSquaresParam3 and the two children that decompose
MagicSquares.magic_count_three_divisible."""
import io
import json
import os
import subprocess
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PY = r"C:/Users/anche/.workbuddy/binaries/python/versions/3.13.12/python.exe"
API = os.path.join(ROOT, "scripts", "p2m_api.py")
MS = os.path.join(ROOT, "missions", "magic-squares")


def run(*args):
    return subprocess.run([PY, API] + list(args), cwd=ROOT,
                          capture_output=True, text=True).stdout


def jget(path, query=""):
    out = run("get", path, query) if query else run("get", path)
    try:
        return json.loads(out)
    except Exception:
        return {"_raw": out[:400]}


def main():
    # ---- 1. publish the definition -------------------------------------
    src = io.open(os.path.join(ROOT, "Definitions", "Def_MagicSquaresParam3.lean"),
                  encoding="utf-8").read()
    nl = r"""The MacMahon parametrization of $3 \times 3$ magic squares.

Let $M$ be a $3\times3$ array of nonnegative integers whose three rows, three
columns and two main diagonals all sum to $s = 3e$. MacMahon's centre identity
gives $M_{11} = e$, and then the eight line identities force

$$M \;=\; \begin{pmatrix}
a & 3e-a-c & c \\
e+c-a & e & e+a-c \\
2e-c & a+c-e & 2e-a
\end{pmatrix},
\qquad a = M_{00},\; c = M_{02}.$$

So the square is determined by the pair $(a,c)$, and all nine entries are
nonnegative precisely when

$$e \le a + c \le 3e, \qquad a \le e + c, \qquad c \le e + a .$$

These inequalities imply $0 \le a, c \le 2e$: adding $a + c \le 3e$ to
$a \le e + c$ yields $2a \le 4e$, and symmetrically for $c$. Substituting
$p = a - e$, $q = c - e$, the four inequalities become $|p+q| \le e$ and
$|p-q| \le e$, equivalently $|p| + |q| \le e$; hence the admissible pairs are in
bijection with the $\ell_{1}$ ball of radius $e$ in $\mathbb{Z}^{2}$, which has
$$1 + 4\sum_{k=1}^{e} k \;=\; 2e^{2} + 2e + 1$$
lattice points. This is MacMahon's count $M_{3}(3e) = 2e^{2} + 2e + 1$.

**Formalization Note** `mkMagic3 e a c` builds the array above using truncated
natural-number subtraction; the row/column/diagonal identities only hold under
the admissibility inequalities, which are collected in `IsParam3 e a c`.
`paramSet e` is the finite set of admissible pairs, searched inside the lossless
box $[0,2e] \times [0,2e]$, and `paramCount e` is its cardinality. Both
`paramSet` and `paramCount` are `noncomputable` because membership in `paramSet`
involves a decidable proposition."""
    payload = dict(
        definition_name="MagicSquaresParam3",
        definition_title="MacMahon parametrization of 3x3 magic squares",
        definition=src,
        natural_language_statement=nl,
        source="P. A. MacMahon, Combinatory Analysis (1915); see also G. Xin, "
               "Constructing all magic squares of order three, Electron. J. Combin. "
               "(2008), and Beck-Cohen-Cuomo-Gribelyuk, Amer. Math. Monthly 110 (2003).",
        tags=["combinatorics", "magic-squares", "enumerative-combinatorics"],
    )
    p = os.path.join(MS, "submit-definition-param3.json")
    json.dump(payload, io.open(p, "w", encoding="utf-8"), ensure_ascii=False, indent=1)
    print(run("post", "/submit-definition", p).split("\n", 1)[1][:600])

    # ---- 2. publish the two children ------------------------------------
    PRE = ("import Mathlib\nimport Definitions.Def_MagicSquares\n"
           "import Definitions.Def_MagicSquaresParam3\nopen MagicSquares")
    children = [
        dict(
            theorem_name="MagicSquares.magic_three_param_bij",
            theorem_title="MacMahon parametrization: 3x3 magic squares vs admissible pairs",
            formal_statement=(
                "namespace MagicSquares\n\n"
                "theorem magic_three_param_bij (e : \u2115) :\n"
                "    magicCount 3 (3 * e) = paramCount e := by sorry\n\n"
                "end MagicSquares"
            ),
            natural_language_statement=r"""The map
$$M \longmapsto (M_{00},\, M_{02})$$
is a bijection from the $3 \times 3$ magic squares with nonnegative entries and
line sum $3e$ onto the admissible parameter pairs
$$\{(a,c) \in \mathbb{N}^{2} : e \le a + c \le 3e,\; a \le e + c,\; c \le e + a\}.$$
Consequently the two counting functions agree: $M_{3}(3e) = \mathrm{paramCount}(e)$.

**Injectivity.** MacMahon's centre identity gives $M_{11} = e$; then the diagonal
and anti-diagonal identities give $M_{22} = 2e - a$ and $M_{20} = 2e - c$, the row
and column identities fill in $M_{01} = 3e - a - c$, $M_{21} = a + c - e$,
$M_{10} = e + c - a$, $M_{12} = e + a - c$, and $M_{02} = c$, $M_{00} = a$ by
definition. So $(a,c)$ determines $M$ completely.

**Surjectivity.** Given an admissible pair, the array `mkMagic3 e a c` has
nonnegative entries (that is exactly what admissibility says, together with the
implied bounds $a, c \le 2e$) and its three rows, three columns and two diagonals
all sum to $3e$; each entry is at most $3e$, so it lies in the search space
$\{0,\dots,3e\}$ used by `magicCount`.

**Formalization Note** `magicCount 3 (3*e)` counts arrays with entries in
`Fin (3*e+1)`; `paramCount e` counts the finset `paramSet e`. The bijection is
expressed as an equality of cardinalities.""",
            source="P. A. MacMahon, Combinatory Analysis (1915); G. Xin, Constructing all "
                   "magic squares of order three (2008).",
        ),
        dict(
            theorem_name="MagicSquares.param_three_card",
            theorem_title="Counting admissible MacMahon parameters for 3x3 squares",
            formal_statement=(
                "namespace MagicSquares\n\n"
                "theorem param_three_card (e : \u2115) :\n"
                "    paramCount e = 2 * e ^ 2 + 2 * e + 1 := by sorry\n\n"
                "end MagicSquares"
            ),
            natural_language_statement=r"""The number of admissible MacMahon parameter pairs for
line sum $3e$ is
$$\mathrm{paramCount}(e) \;=\; \#\{(a,c) \in \mathbb{N}^{2} : e \le a+c \le 3e,\;
a \le e+c,\; c \le e+a\} \;=\; 2e^{2} + 2e + 1 .$$

**Proof.** Substituting $p = a - e$ and $q = c - e$, the four inequalities read
$|p+q| \le e$ and $|p-q| \le e$, and since
$\max(|p+q|,|p-q|) = |p| + |q|$ this is exactly $|p| + |q| \le e$: the
$\ell_{1}$ ball of radius $e$ in $\mathbb{Z}^{2}$. On the sphere
$|p| + |q| = k$ there are $4k$ lattice points for $k \ge 1$ and one for $k = 0$,
so the ball has
$$1 + \sum_{k=1}^{e} 4k \;=\; 1 + 2e(e+1) \;=\; 2e^{2} + 2e + 1$$
points.

Equivalently one may sum over $a$: for fixed $a \in [0,2e]$ the admissible $c$
form the interval $[\,|a-e|,\ \min(a+e,\,3e-a)\,]$, which has $2a+1$ elements when
$a \le e$ and $4e-2a+1$ elements when $a \ge e$; summing gives
$(e+1)^{2} + e^{2} = 2e^{2} + 2e + 1$.

**Formalization Note** `paramCount e` is the cardinality of the finset
`paramSet e`, defined by filtering the box $[0,2e] \times [0,2e]$ — the bounds
$a, c \le 2e$ are implied by admissibility, so this is lossless.""",
            source="P. A. MacMahon, Combinatory Analysis (1915): $M_3(t) = "
                   "\\tfrac{2}{9}t^2 + \\tfrac{2}{3}t + 1$ for $3 \\mid t$.",
        ),
    ]
    payload = {"problems": []}
    for c in children:
        d = dict(c)
        d["preamble"] = PRE
        d["tags"] = ["combinatorics", "magic-squares", "enumerative-combinatorics"]
        payload["problems"].append(d)
    p = os.path.join(MS, "submit-problems-batch3.json")
    json.dump(payload, io.open(p, "w", encoding="utf-8"), ensure_ascii=False, indent=1)
    print(run("post", "/submit-problem", p).split("\n", 1)[1][:1500])


if __name__ == "__main__":
    main()
