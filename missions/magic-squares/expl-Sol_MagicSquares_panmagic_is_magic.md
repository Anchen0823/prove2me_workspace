## Every panmagic square is magic

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
with the additive structure used to speak of offsets.