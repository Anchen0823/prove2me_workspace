# -*- coding: utf-8 -*-
"""Submit the two nodes of the order-three classification mission."""
import io, json, os, subprocess, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PY = sys.executable
API = os.path.join(ROOT, "scripts", "p2m_api.py")
OUT = os.path.join(ROOT, "missions", "normal3")

PRE = ("import Mathlib\nimport Definitions.Def_MagicSquares\n"
       "import Definitions.Def_MagicSquaresParam3\nopen MagicSquares")
SRC = ("P. A. MacMahon, Combinatory Analysis (1916); W. S. Andrews, Magic Squares and "
       "Cubes, 2nd ed., Dover, 1960; M. Beck, T. Cohen, J. Cuomo, P. Gribelyuk, "
       "Amer. Math. Monthly 110 (2003), 707-717; arXiv:math/0201013v3.")

LIST8 = ("(a = 2 ∧ c = 4) ∨ (a = 2 ∧ c = 6) ∨ (a = 4 ∧ c = 2) ∨ (a = 4 ∧ c = 8) ∨\n"
         "        (a = 6 ∧ c = 2) ∨ (a = 6 ∧ c = 8) ∨ (a = 8 ∧ c = 4) ∨ (a = 8 ∧ c = 6)")

P_CLASSIFY = {
 "theorem_name": "MagicSquares.magic_three_normal_classify",
 "theorem_title": "The normal members of MacMahon's order-three family",
 "formal_statement": ("namespace MagicSquares\n\n"
   "theorem magic_three_normal_classify (a c : ℕ) (hac : (a, c) ∈ paramSet 5) :\n"
   "    IsNormal (mkMagic3 5 a c) ↔\n"
   "      " + LIST8 + " := by sorry\n\n"
   "end MagicSquares"),
 "natural_language_statement": r"""**Characterization of the normal squares inside
MacMahon's order-three family.**

For $(a,c)\in\mathrm{paramSet}\ 5$,

$$\mathrm{mkMagic3}(5,a,c)\ \text{is normal}\iff (a,c)\in\{(2,4),(2,6),(4,2),(4,8),(6,2),(6,8),(8,4),(8,6)\}.$$

Here *normal* means the nine entries lie in $[1,9]$ and are pairwise distinct,
i.e. they are a permutation of $1,\dots,9$; and

$$\mathrm{mkMagic3}(5,a,c)=
\begin{pmatrix}
a & 15-a-c & c\\
5+c-a & 5 & 5+a-c\\
10-c & a+c-5 & 10-a
\end{pmatrix}.$$

**Proof.** Normality forces $1\le a\le 9$ and $1\le c\le 9$, since $a=M_{00}$ and
$c=M_{02}$ are entries. This leaves $81$ pairs, each of which is a ground
instance and is settled by evaluation. The eight surviving pairs are exactly
those for which the corner entries $a$ and $c$ are distinct members of
$\{2,4,6,8\}$ with $a+c\ne 10$; the pairs with $a+c=10$ are excluded because
then $M_{21}=a+c-5=5$ coincides with the centre.

**Formalization Note** `IsNormal` is stated with a `Function.Injective`, which is
not decidable as given, so it is first rewritten into an explicit conjunction of
entrywise bounds over `Fin 3` and pairwise-distinctness of the nine positions.
The quantifiers over `Fin 3` are then unfolded with `Fin.forall_fin_succ` before
`norm_num` decides the resulting ground instances. Because the parametrization
is over $\mathbb{N}$, entries such as $a+c-5$ and $15-a-c$ truncate at zero, and
each instance is evaluated with the truncation in place.""",
 "preamble": PRE, "source": SRC,
 "tags": ["combinatorics", "magic-squares", "enumerative-combinatorics"],
}

P_EIGHT = {
 "theorem_name": "MagicSquares.magic_three_normal_eight",
 "theorem_title": "There are exactly eight normal magic squares of order three",
 "formal_statement": ("namespace MagicSquares\n\n"
   "theorem magic_three_normal_eight :\n"
   "    ((paramSet 5).filter fun ac => IsNormal (mkMagic3 5 ac.1 ac.2)).card = 8 := by sorry\n\n"
   "end MagicSquares"),
 "natural_language_statement": r"""**Lo Shu uniqueness.** Exactly eight admissible
parameter pairs give a normal magic square of order three:

$$\#\{(a,c)\in\mathrm{paramSet}\ 5:\ \mathrm{mkMagic3}(5,a,c)\ \text{normal}\}=8.$$

By `magic_three_param_bij`, the admissible parameter pairs are in bijection with
the $3\times3$ magic squares of line sum $15$, so this is precisely the statement
that there are **eight** normal magic squares of order three — the eight images
of

$$\begin{pmatrix}4&9&2\\3&5&7\\8&1&6\end{pmatrix}$$

under the symmetry group $D_{4}$ of the square. Equivalently: the Lo Shu square
is the *unique* normal magic square of order three up to symmetry.

This is the oldest non-trivial classification in combinatorics, and the reason
order three is exceptional: for $n=4$ there are $880$ normal squares up to
symmetry, and for $n\ge5$ no classification is known.

**Proof.** Immediate from `magic_three_normal_classify`: the filter selects
exactly the eight listed pairs, and the eight pairs are distinct.""",
 "preamble": PRE, "source": SRC,
 "tags": ["combinatorics", "magic-squares", "enumerative-combinatorics"],
}

def main():
    payload = {"problems": [P_CLASSIFY, P_EIGHT]}
    path = os.path.join(OUT, "submit-problems-batch1.json")
    with io.open(path, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, ensure_ascii=False, indent=1)
    r = subprocess.run([PY, API, "post", "/submit-problem", path], cwd=ROOT,
                       capture_output=True, text=True)
    print(r.stdout[:2500])
    print(r.stderr[:600])

if __name__ == "__main__":
    main()
