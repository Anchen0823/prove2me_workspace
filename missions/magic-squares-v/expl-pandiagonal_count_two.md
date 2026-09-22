## The order-two pandiagonal count: $P_{2}=M_{2}$

Here $P_{n}(t)$ counts pandiagonal squares in the counting-theory sense of `IsPandiagonal`:
semi-magic, and the wrapped diagonals parallel to the main diagonal all summing to the line sum.

At order two there are two such diagonals, of offsets $0$ and $1$. The offset-$0$ one is
$M_{00}+M_{11}$, the main diagonal; the offset-$1$ one is $M_{01}+M_{10}$, the anti-diagonal.
So the pandiagonal condition is literally the magic condition for $n=2$, and
`symmetricMagicSquares`-style coincidence holds: `pandiagonalSquares 2 t = magicSquares 2 t`,
giving $P_{2}(t)=1$ for even $t$ and $0$ otherwise.

**Context.** Order two is the last order at which the two readings of "pandiagonal" agree. From
order three on they diverge sharply: the one-direction reading gives $P_{3}(t)=\binom{t+2}{2}$
(never zero), while the two-direction reading `IsPanMagic` leaves only the constant square and
vanishes off multiples of three. Compare `pandiagonal_count_three` and `panmagic_count_three`.

### Formalization notes

* The set equality is proved by extensionality. Both directions are `fin_cases` on the offset
  `k : Fin 2` followed by `simpa [brokenDiagSum, diagSum]` / `simpa [brokenDiagSum, antiDiagSum]`;
  these are `simp`-based, so the Fin-index representation causes no difficulty.
* As in the symmetric case, the order-two magic count is inlined as a private helper so the file
  stands alone.
