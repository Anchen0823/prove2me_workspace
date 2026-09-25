# -*- coding: utf-8 -*-
"""Create the fourth magic-squares mission: the special classes of order three
(panmagic and symmetric magic squares)."""
import io, json, os, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
PY = sys.executable
API = os.path.join(ROOT, "scripts", "p2m_api.py")
OUT = os.path.join(ROOT, "missions", "magic-squares-iv")
FIELD_COMBINATORICS = "55eec41b-ff24-45ad-96b6-49d7a6869286"

DESCRIPTION = r"""## Motivation

The first three missions in this programme $3\times3$ magic squares end to end:
Mission I proved MacMahon's count $M_{3}(3e)=2e^{2}+2e+1$, Mission II his
semi-magic count $H_{3}(t)=3\binom{t+3}{4}+\binom{t+2}{2}$, and Mission III
classified the *normal* squares (Lo Shu uniqueness). All three work with the
plain magic condition.

This mission counts the two **special classes** that are singled out by requiring
*more* than magicness, in the opposite directions one expects:

* the **panmagic** (pandiagonal) squares, whose broken diagonals must also have
  the magic sum — a strengthening so strong that for order three the whole
  family collapses;
* the **symmetric** magic squares, whose array must equal its transpose — a
  symmetry that only removes a few conditions and leaves a genuine family.

Writing $P_{3}(t)$ and $S_{3}(t)$ for the two counting functions, the goal is to
determine both for every line sum $t$:

$$P_{3}(t)=\begin{cases}1,&3\mid t\\ 0,&3\nmid t\end{cases},
\qquad
S_{3}(t)=\begin{cases}\dfrac{2t}{3}+1,&3\mid t\\[2mm] 0,&3\nmid t\end{cases}.$$

## Setting

Everything is built on the vocabulary of `MagicSquares` (Mission I):

* `IsPanMagic` — semi-magic, and every broken diagonal in both directions has
  the line sum, indices read modulo $n$;
* `IsSymmetric` — $M_{ij}=M_{ji}$;
* `panMagicCount`, `symmetricMagicCount` — the cardinalities of the two filtered
  finsets of arrays over `Fin (t+1)`, which is lossless because every entry of a
  square of line sum $t$ is at most $t$.

The new definition module `MagicSquaresSpecial3` records the two explicit shapes
that the proofs produce: `constSquare3 e` (the array all of whose entries are
$e$, read over the ambient `Fin (3e+1)`) and

$$\mathrm{symmMagic3}(e,a)=\begin{pmatrix}
a & 2e-a & e\\ 2e-a & e & a\\ e & a & 2e-a\end{pmatrix},$$

together with the parameter set `symmParamSet e` $=\{0,\dots,2e\}$ and its
cardinality `symmParamCount e`.

## Formalization targets

### Goal — the complete count

`special_three_count`: for every natural number $t$, the pair of equalities
displayed above. The proof splits on $3\mid t$ and reduces to four child nodes.

### The route

1. **Panmagic collapses to the constant square** (`pan_three_card`). Writing the
   array as $a,b,c;d,m,f;g,h,i$, the twelve line equations form a linear system
   whose only nonnegative solution is $a=b=\dots=i=e$. So $P_{3}(3e)=1$.
2. **Symmetry is classified by a corner** (`symmetric_magic_three_classify`).
   Symmetry identifies three pairs of entries, leaving five free cells and five
   line equations; the anti-diagonal $2c+m=3e$ forces $c=m=e$, and the rows give
   $M=\mathrm{symmMagic3}(e, M_{00})$.
3. **A bijection onto an interval** (`symm_three_bij`). Sending a symmetric magic
   square of line sum $3e$ to $M_{00}$ is a bijection onto
   $\{0,1,\dots,2e\}$; hence $S_{3}(3e)=2e+1$.
4. **The divisibility obstruction** (`pan_three_otherwise`,
   `symm_three_otherwise`). Both classes consist of magic squares, and an
   order-three magic square has centre $t/3$ (`center_of_order_three`), so
   $3\nmid t$ forces both counts to vanish.

## Significance

*The results.* The three order-three counts behave completely differently in the
same parameter: MacMahon's $M_{3}$ is quadratic, the symmetric count is linear,
and the panmagic count is constant. That contrast is the point of the order-three
study — order three is small enough to be completely understood, and the special
classes show how differently the two natural strengthenings of the magic
condition act. It is also exactly what is lost at order four, where no closed
form is known for any of the three.

*Formalizing them.* The mathematical content is elementary, but the two classes
require genuinely different proof techniques, which is what makes the mission
worth formalizing:

- For the panmagic case the six broken diagonals together with the rows and
  columns give a **subtraction-free** linear system over $\mathbb{N}$, so the
  uniqueness step is a single `omega` call. The only work is exposing the twelve
  equations, which requires reducing the index arithmetic $i+k$ and
  $\mathrm{rev}(i)+k$ on `Fin 3`.
- For the symmetric case the answer is a *family*, and the admissibility bound
  $a\le 2e$ is a statement about **truncated subtraction**: the entry $2e-a$ is
  computed in $\mathbb{N}$, so the row identity $a+(2e-a)+e=3e$ is satisfiable
  precisely for $a\le 2e$. Formalizing the bijection therefore needs an honest
  treatment of that truncation, where the panmagic case needs none.

## Difficulty

*Truncated subtraction, in the admissibility direction.* The classification
`M = symmMagic3 e (M 0 0)` is true for every $M$, without any bound on $M_{00}$;
the bound only appears when asking which members of the family are squares of
line sum $3e$. Keeping those two statements apart is what makes the bijection
proof manageable: classification is a pure `omega` computation, while
admissibility is a one-line argument that $a+(2e-a)=2e$ forces $a\le 2e$.

*Finite but not decidable.* `panMagicCount` and `symmetricMagicCount` are
cardinalities of filtered finsets over a function type, so the proofs cannot be
`decide` or `norm_num` — the platform forbids `native_decide` in any case. Both
counting theorems are therefore stated as `Finset.card_bij` / `card_eq_one`
arguments over explicit bijections, not as finite evaluations.

## Formalization scope

* The in-scope statements are the two closed forms for all $t$, together with the
  classification of the symmetric family that the bijection is built on.
* Parametrization follows MacMahon; the symmetric shape is the diagonal slice
  $c=e$ of his two-parameter family, which is why the count drops from
  quadratic to linear.
* Nothing here re-proves Mission I: the divisibility obstruction is inherited
  from the already-proved `center_of_order_three`.
* Reusable beyond this mission: the order-three classification of symmetric magic
  squares, the observation that panmagic order-three squares are exactly the
  constant ones, and the technique of discharging twelve-index linear systems
  over `Fin 3` with a single `omega`.

## Selected references

- P. A. MacMahon, *Combinatory Analysis*, Vol. II, Cambridge University Press, 1916.
- M. Beck, T. Cohen, J. Cuomo and P. Gribelyuk, *The number of "magic" squares, cubes and hypercubes*, Amer. Math. Monthly **110** (2003), 707--717. <https://arxiv.org/abs/math/0201013>
- W. S. Andrews, *Magic Squares and Cubes*, 2nd ed., Dover, 1960.
- H. Behforooz, *Symmetric and panmagic squares* (survey of the symmetry
  properties of magic squares), and the standard pandiagonal literature.
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
        "name": "Magic Squares IV: The Special Classes of Order-Three Magic Squares",
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
