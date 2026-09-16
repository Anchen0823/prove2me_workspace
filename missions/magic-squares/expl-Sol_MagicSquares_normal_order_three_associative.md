## A normal $3 \times 3$ magic square is associative with constant $10$

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
magic square with line sum $15$ is associative with constant $10$.