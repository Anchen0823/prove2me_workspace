# -*- coding: utf-8 -*-
"""Create the magic-squares mission proposal and seed it with items.

Long proof paths (MacMahon's enumeration) are managed as a mission so the
decomposition DAG is explicit and curated, instead of a pile of loose
reductions.
"""
import io
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
PY = sys.executable
API = os.path.join(ROOT, "scripts", "p2m_api.py")

FIELD_COMBINATORICS = "55eec41b-ff24-45ad-96b6-49d7a6869286"

# already-published platform nodes
DEF_MAGIC = "be2f2b6a-a540-47ae-b487-ac22532a2745"
DEF_PARAM3 = "68eaae9b-d759-4a2a-83f6-741ecdbca5f8"
THM_CENTER = "ebbc5687-663f-472d-afb6-f760546652db"
THM_OPPOSITE = "695c1fc5-a4a3-4ee4-9eda-9a132228ba46"
THM_BIJ = "f62c9364-c183-42f8-84b8-a6ac8e72ade7"
THM_CARD = "8063946a-dd43-4ff9-9107-f3e4d7cb040b"
THM_GOAL = "393a2adc-5e8e-4847-b9c6-f7b141a5114e"

DESCRIPTION = r"""## Motivation

Counting **magic squares** — arrays of nonnegative integers whose rows, columns
and two main diagonals all share a common line sum — is one of the oldest
problems in enumerative combinatorics, and the testing ground on which the
general theory was built. MacMahon computed the order-three count in 1915 by
hand; sixty years later Stanley, and then Beck, Cohen, Cuomo and Gribelyuk
([*Amer. Math. Monthly* **110** (2003), 707--717](https://arxiv.org/abs/math/0201013)),
showed that for *general* order $n$ the counting functions are
**quasi-polynomials** in the line sum, by identifying them with Ehrhart
quasi-polynomials of rational polytopes. The order-three case is the oldest
nontrivial instance of that theory and the one where every step can still be
checked by hand.

The subject therefore has a curious status: the enumerative answer for $n=3$ has
been known for over a century, and the *structural* facts behind it (a
$3\times3$ magic square is determined by two corner entries; opposite cells sum
to twice the centre) are folklore — but none of it has a machine-checked proof.
This mission formalizes the classical derivation end to end.

## Setting

Fix an order $n$ and a type $\alpha$ of entries. A **square** of order $n$ is an
$n\times n$ array $M$ with entries in $\alpha$; its **row sums**, **column
sums**, and the two **diagonal sums** (main and anti-diagonal) are the sums of
the entries along those lines.

* $M$ is **semi-magic** with line sum $s$ if every row and every column sums to
  $s$.
* $M$ is **magic** with line sum $s$ if in addition both main diagonals sum to
  $s$.
* $M$ is **panmagic** (pandiagonal) if every *broken* diagonal, in both
  directions, also sums to $s$.

No distinctness of entries is required. Let $H_n(t)$ denote the number of
semi-magic and $M_n(t)$ the number of magic squares of order $n$ with
nonnegative integer entries and line sum $t$. Every entry of such a square is at
most $t$, so these are finite counts.

For $n=3$ the whole family is parametrized. If $M$ has line sum $3e$ then the
centre cell equals $e$, and writing $a=M_{00}$ and $c=M_{02}$ the eight line
identities force

$$
M=\begin{pmatrix}
a & 3e-a-c & c\\
e+c-a & e & e+a-c\\
2e-c & a+c-e & 2e-a
\end{pmatrix}.
$$

All nine entries are nonnegative exactly when

$$
e\le a+c\le 3e,\qquad a\le e+c,\qquad c\le e+a,
$$

and substituting $p=a-e$, $q=c-e$ turns these into $|p|+|q|\le e$: the
$\ell_1$ ball of radius $e$ in $\mathbb{Z}^2$.

## Formalization targets

### Goal — MacMahon's count

$$M_{3}(3e)\;=\;2e^{2}+2e+1 ,$$

together with the companion vanishing $M_3(t)=0$ when $3\nmid t$. This is the
count of $3\times3$ **magic** squares of line sum $3e$ with nonnegative integer
entries (entries need not be distinct). It is the goal because it is the
weakest stable statement: it asserts only the shape of the answer, not the
intermediate parametrization, and it survives verbatim as the $n=3$ case of the
general quasi-polynomial theorem.

### Stronger — the parametrization itself

That the map $M\mapsto(M_{00},M_{02})$ is a **bijection** from the $3\times3$
magic squares of line sum $3e$ onto the admissible parameter pairs, and that the
latter are counted by the $\ell_1$-ball cardinality. This is the route the
mission actually takes; the count is its corollary.

### Further — semi-magic counts

$H_3(t)$, the analogous count for **semi-magic** squares, is a genuinely
different and harder quasi-polynomial. It is listed as a stretch target, not a
milestone.

## Significance

*The result itself.* MacMahon's formula is the base case of the Ehrhart-theory
reading of magic-square enumeration; Beck--Cohen--Cuomo--Gribelyuk's
quasi-polynomial theorem for general $n$ degenerates to it at $n=3$, so it is
the sanity check any generalization must pass. The parametrization behind it is
what makes the "how many" question finite-dimensional at all: it reduces a
search over $t^9$ arrays to a count of lattice points in a two-dimensional ball.
Downstream, the same parametrization governs the classification of *normal*
$3\times3$ magic squares (the Lo Shu square and its symmetries) and the
associativity identity $M_{ij}+M_{2-i,2-j}=2M_{11}$.

*Formalizing it.* The mathematics is classical and **proved**; nothing here is
open. What is missing is the **formalized** artifact. The order-three structural
lemmas — the centre identity, the opposite-cell identity, and the two directions
of the parametrization — are already machine-checked on this platform. The
remaining work is the *counting* step: exhibiting a concrete bijection between
two finsets whose elements live in different types (arrays over `Fin (3e+1)`
versus pairs of naturals) and evaluating a finite sum. That is where the
formalization, not the mathematics, is hard.

## Difficulty

The obvious attack — "each magic square is determined by $(a,c)$, so just count
the pairs" — fails at exactly one point, and it is not a mathematical point. The
counting function $M_3$ is defined as the cardinality of a finset of arrays with
entries in `Fin (3e+1)` (a *finite* type, so that `Finset.univ` exists), whereas
the parametrization lives over $\mathbb{N}$. Proving the counts agree therefore
requires a honest `Finset.card_bij` in **both** directions:

* forward, extract $(M_{00},M_{02})$ from an array and show the pair is
  admissible;
* backward, build `mkMagic3` from an admissible pair, coerce every entry into
  `Fin (3e+1)` using the bound $M_{ij}\le 2e\le 3e$, and show the round trip is
  the identity.

Neither direction is deep, but the coercions are unforgiving: a truncated
subtraction in `mkMagic3` is only correct because admissibility forbids the
truncation, and that side condition must be discharged explicitly rather than
assumed. The second difficulty is the cardinality of the $\ell_1$ ball: the
identification $|p+q|\le e\ \wedge\ |p-q|\le e\ \Longleftrightarrow\
|p|+|q|\le e$ needs the elementary identity
$\max(|p+q|,|p-q|)=|p|+|q|$, after which the count is
$1+4\sum_{k=1}^e k = 2e^2+2e+1$.

## Formalization scope

* Entries are indexed by `Fin n`; the anti-diagonal uses `Fin.rev`, and broken
  diagonals use addition modulo $n$. Counting functions are cardinalities of
  finsets of arrays over `Fin (t+1)` — lossless, since every entry is at most
  $t$ — and return natural numbers.
* `mkMagic3` is defined over $\mathbb{N}$ with **truncated** subtraction. Every
  row/column/diagonal identity therefore carries the admissibility inequalities
  as explicit hypotheses; no identity is asserted unconditionally.
* Trivializing formalizations are ruled out: the goal is not a statement about a
  hardcoded small $e$, nor about a finset declared to have the right
  cardinality. The count must be *derived*.
* Reusable beyond this mission: the core vocabulary (`Square`, `IsSemiMagic`,
  `IsMagic`, `IsPanMagic`, `IsAssociative`, `IsNormal`, `magicConstant`, and the
  four counting functions $H_n,M_n,P_n,S_n$), the symmetry/affine toolbox, and
  the order-three structural lemmas. Contributions are welcome on the
  semi-magic count $H_3$, on panmagic and associative refinements, and on the
  extension to general $n$.

## Selected references

- P. A. MacMahon, *Combinatory Analysis*, Vol. II, Cambridge University Press, 1916 (the $M_3$ formula dates to his 1915 work).
- M. Beck, T. Cohen, J. Cuomo and P. Gribelyuk, *The number of "magic" squares, cubes and hypercubes*, Amer. Math. Monthly **110** (2003), 707--717. <https://arxiv.org/abs/math/0201013>
- M. Beck and T. Zaslavsky, *Six little squares and how their numbers grow*, J. Combin. Theory Ser. A **113** (2006). <https://arxiv.org/abs/math/0502370>
- G. Xin, *Constructing all magic squares of order three*, Discrete Math. **308** (2008). <https://arxiv.org/abs/math/0610771>
"""


def api(*args):
    out = subprocess.run([PY, API] + list(args), cwd=ROOT,
                         capture_output=True, text=True)
    txt = out.stdout
    # strip the leading status-code line if present
    lines = txt.splitlines()
    start = 0
    for idx, ln in enumerate(lines):
        if ln.strip().startswith("{"):
            start = idx
            break
    body = "\n".join(lines[start:])
    try:
        return json.loads(body)
    except Exception:
        return {"_raw": txt}


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "items":
        pid = io.open(os.path.join(ROOT, "missions", "magic-squares", "proposal_id.txt"),
                      encoding="utf-8").read().strip()
    else:
        payload = {
            "name": "Magic Squares I: MacMahon's Enumeration of Order-Three Magic Squares",
            "description": DESCRIPTION,
            "mission_type": "ResearchPaper",
            "field_ids": [FIELD_COMBINATORICS],
        }
        path = os.path.join(ROOT, "missions", "magic-squares", "proposal-create.json")
        with io.open(path, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, ensure_ascii=False, indent=1)
        res = api("post", "/mission-proposals", path)
        print(json.dumps(res, ensure_ascii=False)[:1500])
        if "id" not in res:
            return
        pid = res["id"]
        with io.open(os.path.join(ROOT, "missions", "magic-squares", "proposal_id.txt"),
                     "w", encoding="utf-8") as fh:
            fh.write(pid)
        print("proposal id:", pid)
    return pid


if __name__ == "__main__":
    main()
