#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""Submit the batch-2 magic-square proofs, each with a mathematical explanation."""
import io
import json
import os
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PY = sys.executable
API = os.path.join(ROOT, "scripts", "p2m_api.py")

ITEMS = [
    dict(
        tid="08463353-63d3-4260-89cf-9f61e97f7a04",
        sol="Solutions/Sol_MagicSquares_normal_order_three_constant.lean",
        expl=r"""## The magic constant of a normal $3 \times 3$ magic square is $15$

A normal square of order $n$ uses each of $1, \dots, n^{2}$ exactly once, so the
sum of all its entries is
$$1 + 2 + \cdots + n^{2} = \frac{n^{2}(n^{2}+1)}{2}.$$
On the other hand, adding up the $n$ rows counts every entry once, so the same
total equals $n s$. Hence $2ns = n^{2}(n^{2}+1)$, and for $n > 0$ we may cancel
one factor $n$ to obtain the classical identity
$$2s = n\,(n^{2}+1).$$
Putting $n = 3$ gives $2s = 3 \cdot 10 = 30$, i.e. $s = 15$.

The degenerate case $n = 0$ is vacuous (there are no rows), and there the diagonal
condition forces $s = 0$ anyway, so the cancellation is legitimate for every $n$.

### How this maps onto the Lean code

The heavy lifting is done by the imported child
`MagicSquares.magic_constant_of_normal`, which is the general identity above.
The reduction simply instantiates it at $n = 3$:

```lean
have h := magic_constant_of_normal 3 M s hN hM   -- h : 2 * s = 3 * (3 ^ 2 + 1)
norm_num at h                                    -- h : 2 * s = 30
omega                                            -- s = 15
```

`norm_num` discharges the arithmetic $3^{2} + 1 = 10$, and `omega` solves the
resulting linear Presburger goal over $\mathbb{N}$.""",
    ),
    dict(
        tid="337eccfa-ed88-441d-b7ff-df1c3133fc30",
        sol="Solutions/Sol_MagicSquares_normal_order_three_center_five.lean",
        expl=r"""## The centre of a normal $3 \times 3$ magic square is $5$

Write the square as

$$\begin{matrix} a & b & c \\ d & e & f \\ g & h & i \end{matrix}$$

and let $s$ be the common line sum. Adding the middle row, the middle column and
the two diagonals gives
$$(d+e+f) + (b+e+h) + (a+e+i) + (c+e+g) = 4s .$$
In this sum the centre $e$ is counted four times and every other cell exactly
once, so the left-hand side equals
$$(a+b+\cdots+i) + 3e = 3s + 3e .$$
Therefore $3s + 3e = 4s$, i.e. $3e = s$: **the centre is always one third of the
line sum** (MacMahon, 1915). For a *normal* square we have $s = 15$, so $e = 5$.

### How this maps onto the Lean code

Two already-proved children are imported:

* `MagicSquares.center_of_order_three` — the MacMahon identity $3\,M_{11} = s$;
* `MagicSquares.normal_order_three_constant` — normality forces $s = 15$.

```lean
have hs := normal_order_three_constant M s hN hM   -- hs : s = 15
have hc := center_of_order_three M s hM            -- hc : 3 * M 1 1 = s
omega                                              -- M 1 1 = 5
```

`omega` combines the two linear constraints and concludes $M_{11} = 5$.""",
    ),
    dict(
        tid="3a365b32-43e3-476f-b22c-4151d8274eb8",
        sol="Solutions/Sol_MagicSquares_normal_order_three_associative.lean",
        expl=r"""## A normal $3 \times 3$ magic square is associative with constant $10$

A square is **associative** (also called *regular* or *centre-symmetric*) with
complement constant $c$ when every pair of centrally opposite cells adds to $c$.
Here we show $c = 10$ for every normal $3 \times 3$ magic square.

The reason is a one-line pigeonhole argument. Each centrally opposite pair
$\{M_{ij}, M_{2-i,\,2-j}\}$ sits together with the centre cell $M_{11}$ on a
single magic line — a row (for the pairs $\{M_{10}, M_{12}\}$), a column
($\{M_{01}, M_{21}\}$), the main diagonal ($\{M_{00}, M_{22}\}$) or the
anti-diagonal ($\{M_{02}, M_{20}\}$). Every such line sums to $s = 15$, and the
centre is $5$, so each opposite pair sums to
$$15 - 5 = 10 .$$
The "pair" $\{M_{11}, M_{11}\}$ is covered as well, since $5 + 5 = 10$.

This is the structural backbone of the Lo Shu square: it forces the four corners
to be even and the four edge-middles to be odd, which is the standard starting
point for the classical enumeration of the eight Lo Shu variants.

### How this maps onto the Lean code

The children `normal_order_three_constant` ($s = 15$) and
`center_of_order_three` ($3M_{11} = s$) give $M_{11} = 5$ by `omega`. The eight
line identities are then extracted explicitly:

```lean
have hR0 : M 0 0 + M 0 1 + M 0 2 = s := by
  simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (0 : Fin 3)
...
have hA : M 0 2 + M 1 1 + M 2 0 = s := by
  simpa [antiDiagSum, Fin.sum_univ_three] using hM.2.2
```

`Fin.sum_univ_three` expands a sum over `Fin 3` into its three terms, so each
identity becomes a concrete three-term equation. The goal
`IsAssociative M 10` is `∀ i j, M i j + M (Fin.rev i) (Fin.rev j) = 10`; after
`intro i j` we split the nine index pairs with `fin_cases i <;> fin_cases j`,
`simp [Fin.rev]` reduces the reversal $i \mapsto 2-i$ on `Fin 3` to numerals, and
`omega` closes each of the nine linear goals.

Note that `IsNormal` is in fact not used beyond pinning $s = 15$: any $3\times3$
magic square with line sum $15$ is associative with constant $10$.""",
    ),
    dict(
        tid="1ece0a73-2e26-4db4-9f45-5d2d39f1d53d",
        sol="Solutions/Sol_MagicSquares_panmagic_is_magic.lean",
        expl=r"""## Every panmagic square is magic

Recall the two definitions. A square $M$ of order $n$ is

* **semi-magic** with line sum $s$ when every row and every column sums to $s$;
* **magic** when it is semi-magic and the two main diagonals also sum to $s$;
* **panmagic** (or *pandiagonal*, or *diabolic*) when it is semi-magic and *every
  broken diagonal* in both directions sums to $s$.

The broken descending diagonal of offset $k$ is the set of cells
$\{(i,\, i+k \bmod n) : 0 \le i < n\}$, and the broken ascending diagonal of
offset $k$ is $\{(i,\, n-1-i+k \bmod n) : 0 \le i < n\}$.

For $k = 0$ the broken descending diagonal is exactly the main diagonal
$\{(i,i)\}$, and the broken ascending diagonal is exactly the anti-diagonal
$\{(i,\,n-1-i)\}$. Hence the panmagic condition already contains both diagonal
conditions, and the semi-magic part is shared: panmagic implies magic.

The converse fails in general — the Lo Shu square is magic but not panmagic, and
indeed no normal panmagic square of order $3$ exists. So the two counting
functions $P_{n}(t)$ and $M_{n}(t)$ of Beck–Cohen–Cuomo–Gribelyuk differ, with
$P_{n}(t) \le M_{n}(t)$ pointwise.

### How this maps onto the Lean code

`IsPanMagic M s` is a triple: the semi-magic part `hP.1`, the descending broken
diagonals `hP.2.1 : ∀ k, brokenDiagSum M k = s`, and the ascending ones
`hP.2.2 : ∀ k, brokenAntiDiagSum M k = s`. Evaluating both at the offset
$0 \in \mathrm{Fin}\,n$ and unfolding the definitions turns them into
`diagSum M = s` and `antiDiagSum M = s`:

```lean
constructor
· exact hP.1
constructor
· simpa [diagSum, brokenDiagSum] using hP.2.1 (0 : Fin n)
· simpa [antiDiagSum, brokenAntiDiagSum] using hP.2.2 (0 : Fin n)
```

The index arithmetic $i + 0 = i$ and $\mathrm{rev}(i) + 0 = \mathrm{rev}(i)$ on
`Fin n` is handled by `simp`; the hypothesis `[NeZero n]` is what equips `Fin n`
with the additive structure used to speak of offsets.""",
    ),
]


def main():
    results = []
    for it in ITEMS:
        epath = os.path.join(ROOT, "missions", "magic-squares",
                             "expl-" + os.path.basename(it["sol"]).replace(".lean", ".md"))
        with io.open(epath, "w", encoding="utf-8") as fh:
            fh.write(it["expl"])
        cmd = [PY, API, "verify", it["tid"], os.path.join(ROOT, it["sol"]), "prove", epath]
        out = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True).stdout
        try:
            payload = json.loads(out.split("\n", 1)[1])
            results.append((it["tid"], payload.get("status"), payload.get("submission_id")))
        except Exception:
            results.append((it["tid"], "PARSE_ERROR", out[:200]))
    for r in results:
        print(r)


if __name__ == "__main__":
    main()
