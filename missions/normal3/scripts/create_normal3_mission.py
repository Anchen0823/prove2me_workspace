# -*- coding: utf-8 -*-
"""Create the third magic-squares mission: the complete classification of
order-three magic squares (Lo Shu uniqueness)."""
import io, json, os, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
PY = sys.executable
API = os.path.join(ROOT, "scripts", "p2m_api.py")
OUT = os.path.join(ROOT, "missions", "normal3")
FIELD_COMBINATORICS = "55eec41b-ff24-45ad-96b6-49d7a6869286"

DESCRIPTION = r"""## Motivation

The first two missions in this programme **counted** order-three squares.
Mission I proved MacMahon's magic count $M_{3}(3e)=2e^{2}+2e+1$ and Mission II
his semi-magic count $H_{3}(t)=3\binom{t+3}{4}+\binom{t+2}{2}$. What neither
does is *classify*: counting tells you how many squares there are, but not what
they look like.

This mission closes that gap for the most classical case of all. A **normal**
magic square of order three is a $3\times3$ array containing each of
$1,2,\dots,9$ exactly once, whose rows, columns and two main diagonals all sum
to the magic constant $15$. The statement to be proved is the uniqueness of the
*Lo Shu* square:

> every normal magic square of order three is one of the eight images of
> $\begin{pmatrix}4&9&2\\3&5&7\\8&1&6\end{pmatrix}$ under the symmetry group of
> the square.

In particular there are exactly $8$ of them, and they form a single orbit under
the dihedral group $D_{4}$.

## Setting

MacMahon's parametrization (already formalized in `MagicSquaresParam3`) writes
every order-three magic square of line sum $3e$ as

$$
\mathrm{mkMagic3}(e,a,c)=
\begin{pmatrix}
a & 3e-a-c & c\\
e+c-a & e & e+a-c\\
2e-c & a+c-e & 2e-a
\end{pmatrix},
$$

with $(a,c)$ ranging over the finite admissible set `paramSet e`. For a normal
square the magic constant is $15$, so $e=5$ and the centre entry is $5$.

Normality (`IsNormal`) means every entry lies in $[1,9]$ and the nine entries
are pairwise distinct — equivalently, they are a permutation of $1,\dots,9$.

## Formalization targets

### Goal — Lo Shu uniqueness

$$\\#\\{(a,c)\in \\mathrm{paramSet}\\ 5 : \\mathrm{mkMagic3}(5,a,c)\\ \\text{is normal}\\} = 8,$$

together with the identification of those eight parameter pairs. By the
bijection `magic_three_param_bij` this is exactly the statement that there are
eight normal magic squares of order three, i.e. that Lo Shu is unique up to the
symmetry group of the square.

### The route

1. **Normality bounds the parameters.** If $\mathrm{mkMagic3}(5,a,c)$ is normal
   then $1\\le a\\le 9$ and $1\\le c\\le 9$, because $a$ and $c$ are corner
   entries. This reduces the classification to a finite search over
   $81$ pairs.
2. **Classification** (`magic_three_normal_classify`). Within that range,
   $\mathrm{mkMagic3}(5,a,c)$ is normal exactly when $(a,c)$ is one of
   $$\\{(2,4),(2,6),(4,2),(4,8),(6,2),(6,8),(8,4),(8,6)\\}.$$
   The eight surviving pairs are precisely those with $a,c$ distinct corners of
   the Lo Shu square; the excluded ones are those with $a+c=10$, for which the
   $(2,1)$ entry $a+c-5$ collides with the centre $5$.
3. **Converse** (`magic_three_normal_converse`). Each of the eight pairs really
   does give a normal square.

## Significance

*The result itself.* The uniqueness of Lo Shu is the oldest non-trivial
classification in combinatorics — it is the order-three case of the
classification problem for magic squares, and the reason $n=3$ is special: for
$n=4$ there are $880$ normal squares (up to symmetry) and for $n\ge 5$ no
classification is known. Formalizing it shows that the counting machinery of
Missions I and II can be turned around and used as a *classification* tool: the
parametrization plus a finite verification give the complete list, not just the
cardinality.

*Formalizing it.* The whole proof is a finite case check over $81$ parameter
pairs, so the mathematical content is small and the formalization difficulty is
concentrated in making the finiteness usable. Two things have to be arranged
before automation can see the problem:

- `IsNormal` is stated with a `Function.Injective`, which is **not** decidable
  as stated; it must first be rewritten into an explicit conjunction of
  entrywise bounds and pairwise inequalities over `Fin 3`.
- The quantifiers over `Fin 3` do not unfold by `simp` alone; one needs
  `Fin.forall_fin_succ` to expand them before `norm_num` can decide the
  $81$ resulting ground instances.

## Difficulty

*Finiteness must be manufactured.* Nothing in `IsNormal` mentions a bound on
$a$ or $c$, so the first step is to derive $1\le a,c\le 9$ from the entrywise
bounds of normality. Skipping it leaves an infinite search that `interval_cases`
cannot start.

*Truncated subtraction.* The parametrization is written over $\mathbb{N}$, so
entries such as $a+c-5$ and $15-a-c$ truncate at zero. Every ground instance
must be evaluated with the truncation in place — which is why the classification
is carried out by evaluating the actual entries rather than by manipulating
symbolic inequalities.

## Formalization scope

* Normal means: entries in $[1,n^{2}]$ and pairwise distinct (`IsNormal`).
* The classification is over MacMahon parameters, so it inherits the
  parametrization of `MagicSquaresParam3` and the bijection of Mission I.
* Trivializing formalizations are ruled out: the goal is not a declaration that
  some finite set has eight elements, but a derived classification — normality
  must be *characterized* by an explicit list of parameter pairs.
* Reusable beyond this mission: the decidable reformulation of `IsNormal` for
  `Fin 3` (and the `Fin.forall_fin_succ` technique for unfolding finite
  quantifiers), the list of the eight Lo Shu parameters, and the order-three
  classification itself.

## Selected references

- P. A. MacMahon, *Combinatory Analysis*, Vol. II, Cambridge University Press, 1916.
- M. Beck, T. Cohen, J. Cuomo and P. Gribelyuk, *The number of "magic" squares, cubes and hypercubes*, Amer. Math. Monthly **110** (2003), 707--717. <https://arxiv.org/abs/math/0201013>
- W. S. Andrews, *Magic Squares and Cubes*, 2nd ed., Dover, 1960 (the classical enumeration for $n=4$).
"""


def api(*args):
    out = subprocess.run([PY, API] + list(args), cwd=ROOT,
                         capture_output=True, text=True)
    lines = out.stdout.splitlines()
    start = 0
    for idx, ln in enumerate(lines):
        if ln.strip().startswith("{"):
            start = idx
            break
    try:
        return json.loads("\n".join(lines[start:]))
    except Exception:
        return {"_raw": out.stdout[:800], "_err": out.stderr[:400]}


def main():
    payload = {
        "name": "Magic Squares III: The Complete Classification of Order-Three Magic Squares",
        "description": DESCRIPTION,
        "mission_type": "ResearchPaper",
        "field_ids": [FIELD_COMBINATORICS],
    }
    path = os.path.join(OUT, "proposal-create.json")
    with io.open(path, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, ensure_ascii=False, indent=1)
    res = api("post", "/mission-proposals", path)
    print(json.dumps(res, ensure_ascii=False)[:600])
    if "id" not in res:
        return
    with io.open(os.path.join(OUT, "proposal_id.txt"), "w", encoding="utf-8") as fh:
        fh.write(res["id"])
    print("proposal id:", res["id"])


if __name__ == "__main__":
    main()
