# -*- coding: utf-8 -*-
"""Create the second magic-squares mission: MacMahon's semi-magic count H_3."""
import io
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PY = sys.executable
API = os.path.join(ROOT, "scripts", "p2m_api.py")
OUT = os.path.join(ROOT, "missions", "semi-magic")

FIELD_COMBINATORICS = "55eec41b-ff24-45ad-96b6-49d7a6869286"

DESCRIPTION = r"""## Motivation

This is the second mission in the magic-squares formalization programme, and it
takes up the case the first one deliberately left open.

Counting **semi-magic squares** — arrays of nonnegative integers whose rows and
columns all share a common line sum, with the diagonals unconstrained — is the
"honest" version of the enumeration problem. For order three the *magic* count
$M_{3}(t)$ (mission I) is only a **quasi-polynomial**: it vanishes unless
$3\mid t$ and equals $2e^{2}+2e+1$ on $t=3e$. The **semi-magic** count $H_{3}(t)$
has no such periodicity. MacMahon computed it in 1915:

$$H_{3}(t)\;=\;3\binom{t+3}{4}+\binom{t+2}{2}.$$

It is an honest polynomial in $t$ of degree $4=(3-1)^{2}$, and that degree is
not an accident: Ehrhart and Stanley proved that for every order $n$ the
function $H_{n}(t)$ is a **polynomial** of degree $(n-1)^{2}$ satisfying the
reciprocity law $H_{n}(-n-t)=(-1)^{n-1}H_{n}(t)$. The order-three formula above
is the smallest nontrivial instance of that theorem, and the only one small
enough that every step of the derivation can still be exhibited explicitly.

So this mission is the natural companion to mission I: same objects, same
platform vocabulary, but the counting step is genuinely harder — the parameter
space is four-dimensional rather than two, and the parametrization is *not*
injective until it is normalized.

## Setting

Fix $n$ and a line sum $t$. A **square** of order $n$ is an $n\times n$ array
$M$ of nonnegative integers.

* $M$ is **semi-magic** with line sum $t$ if every row and every column sums to
  $t$. No condition is imposed on the two diagonals, and entries need not be
  distinct.
* $H_{n}(t)$ is the number of such squares. Every entry is at most $t$, so
  $H_{n}(t)$ is the cardinality of a finite set.

For $n=3$ the whole family is governed by the six permutation matrices. Split
them into the three **even** ones — the identity and the two $3$-cycles — whose
supports are the transversals

$$D=\{00,11,22\},\qquad E=\{01,12,20\},\qquad F=\{02,10,21\},$$

and the three **odd** ones — the transpositions — with supports

$$A=\{00,12,21\},\qquad B=\{02,11,20\},\qquad C=\{01,10,22\}.$$

Adding them with multiplicities $u,v,w$ (even) and $x,y,z$ (odd) gives

$$M=\begin{pmatrix} u+x & v+z & w+y\\ w+z & u+y & v+x\\ v+y & w+x & u+z\end{pmatrix},$$

whose six line sums all equal $u+v+w+x+y+z$; so this is a semi-magic square of
line sum $t$ whenever the multiplicities sum to $t$.

## Formalization targets

### Goal — MacMahon's semi-magic count

$$H_{3}(t)\;=\;3\binom{t+3}{4}+\binom{t+2}{2}\qquad\text{for every }t\ge 0 .$$

This is the goal because it is the weakest statement that still pins down the
answer: it asserts the shape of $H_{3}$ without naming the parametrization, and
it survives verbatim as the $n=3$ case of Stanley's theorem that $H_{n}$ is a
polynomial of degree $(n-1)^{2}$.

### The route

1. **Canonical decomposition** (`sm3_canonical`). Every $3\times3$ semi-magic
   square arises from the display above, and the representation becomes unique
   after normalizing: put $u=\min D$, $v=\min E$, $w=\min F$, subtract the
   corresponding even permutation matrices, and the residual odd multiplicities
   satisfy $\min(x,y,z)=0$. The normalization is necessary — without it the
   single relation

   $$D+E+F=A+B+C\;(=J)$$

   identifies distinct $6$-tuples — and it is exactly what makes the count a
   *partition* rather than an inclusion–exclusion.
2. **Bijection** (`sm3_bij`). The map from normalized coefficient vectors to
   semi-magic squares is a bijection, so $H_{3}(t)=\mathrm{sm3Count}(t)$.
3. **Stars and bars** (`comps_card`). The number of $k$-tuples of nonnegative
   integers summing to $n$ is $\binom{n+k-1}{n}$; the case $k=5$ is what the
   count needs.
4. **Evaluating the parameter count** (`sm3_params_card`). Partitioning the
   normalized vectors according to the *first* zero among $(x,y,z)$ writes
   $\mathrm{sm3Count}(t)$ as

   $$\binom{t+4}{4}+\binom{t+3}{4}+\binom{t+2}{4},$$

   which collapses to $3\binom{t+3}{4}+\binom{t+2}{2}$ by two applications of
   Pascal's identity.

## Significance

*The result itself.* $H_{3}$ is the $n=3$ case of a theorem that launched a
subject: Stanley's proof that $H_{n}(t)$ counts lattice points in the
Birkhoff polytope $t\cdot B_{n}$ makes $H_{n}$ an Ehrhart polynomial, and the
order-three formula is the first nontrivial value of it. Beck, Cohen, Cuomo and
Gribelyuk ([*Amer. Math. Monthly* **110** (2003),
707--717](https://arxiv.org/abs/math/0201013)) revisited exactly this
computation on the way to their quasi-polynomial theorem for the *magic* counts,
and Beck and Zaslavsky later pushed the same technique to the panmagic and
symmetric refinements. Getting $H_{3}$ machine-checked therefore validates the
whole hierarchy at its base.

*Formalizing it.* Nothing here is open; the mathematics is a century old. What
is missing is the formalized artifact, and the difficulty is concentrated in two
places that are formalization difficulties rather than mathematical ones.

First, **surjectivity of the permutation-matrix parametrization**. The usual
proof quotes Birkhoff–von Neumann, which in turn needs Hall's marriage theorem.
For order three one can instead do it by hand: subtract the three even
transversal minima and show that the residual satisfies $M_{01}=M_{10}$. That
last step is a six-case argument in linear arithmetic — if $b=M_{01}>c=M_{10}$
then each of the three ways for the transversal $E$ to have minimum zero forces
$c\ge b$ — and it is precisely the kind of step that is invisible on paper and
must be made explicit in a proof assistant.

Second, **the counting step**. The parameter set is a filtered finset of
functions `Fin 6 → Fin (t+1)`, while the formula is stated with binomial
coefficients over $\mathbb{N}$. Connecting them requires stars-and-bars, proved
from scratch (by induction on the number of parts plus the hockey-stick
identity), because the available library results count *sub-multisets* rather
than *compositions*. And the final collapse to MacMahon's form is a chain of
Pascal identities that must be applied in the right order to stay inside
$\mathbb{N}$, where subtraction is truncated.

## Difficulty

Two traps deserve to be named.

*Uniqueness needs the normalization.* The representation by six multiplicities
is *not* injective: $J=D+E+F=A+B+C$. Any formalization that counts $6$-tuples
directly will overcount, and the correction is not a subtraction but a choice of
canonical representative. Deciding "first zero among $(x,y,z)$" is what turns
the count into a genuine partition.

*Truncated subtraction.* The decomposition is expressed over $\mathbb{N}$, so
every identity — in particular the recovery of the multiplicities from a square
— must be stated with the admissibility inequalities as explicit hypotheses. A
truncated subtraction is only correct because normalization forbids the
truncation, and that side condition has to be discharged rather than assumed.

## Formalization scope

* Squares are indexed by `Fin n`; `semiMagicCount n t` is the cardinality of a
  finset of arrays over `Fin (t+1)` — lossless, since every entry is at most
  $t$.
* The parametrization and its normalization are defined over $\mathbb{N}$ with
  truncated subtraction where necessary.
* Trivializing formalizations are ruled out. The goal is not a statement about a
  hardcoded small $t$, nor about a finset declared to have the right
  cardinality: the count must be *derived*, by an explicit bijection followed by
  an explicit evaluation of a finite sum.
* Reusable beyond this mission: the canonical decomposition of $3\times3$
  semi-magic squares (equivalently, the toric description of the order-three
  Birkhoff polytope with its single relation), the stars-and-bars lemma for
  compositions into any number of parts, and the order-three counts themselves.

## Selected references

- P. A. MacMahon, *Combinatory Analysis*, Vol. II, Cambridge University Press, 1916 (the $H_3$ formula dates to his 1915 work).
- M. Beck, T. Cohen, J. Cuomo and P. Gribelyuk, *The number of "magic" squares, cubes and hypercubes*, Amer. Math. Monthly **110** (2003), 707--717. <https://arxiv.org/abs/math/0201013>
- M. Beck and T. Zaslavsky, *Six little squares and how their numbers grow*, J. Combin. Theory Ser. A **113** (2006). <https://arxiv.org/abs/math/0502370>
- R. P. Stanley, *Enumerative Combinatorics*, Vol. I, 2nd ed., Cambridge University Press, 2012 (Ehrhart theory and reciprocity for $H_n$).
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
        return {"_raw": out.stdout[:1200], "_err": out.stderr[:400]}


def main():
    payload = {
        "name": "Magic Squares II: MacMahon's Enumeration of Order-Three Semi-Magic Squares",
        "description": DESCRIPTION,
        "mission_type": "ResearchPaper",
        "field_ids": [FIELD_COMBINATORICS],
    }
    path = os.path.join(OUT, "proposal-create.json")
    with io.open(path, "w", encoding="utf-8") as fh:
        json.dump(payload, fh, ensure_ascii=False, indent=1)
    res = api("post", "/mission-proposals", path)
    print(json.dumps(res, ensure_ascii=False)[:1200])
    if "id" not in res:
        return
    with io.open(os.path.join(OUT, "proposal_id.txt"), "w", encoding="utf-8") as fh:
        fh.write(res["id"])
    print("proposal id:", res["id"])


if __name__ == "__main__":
    main()
