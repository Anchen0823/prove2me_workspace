## No panmagic squares of order three when $3\nmid t$

Let $P_{n}(t)$ be the number of panmagic squares of order $n$ and line sum $t$.
The theorem is the vanishing half of the order-three count:

$$3\nmid t\ \Longrightarrow\ P_{3}(t)=0 .$$

Together with $P_{3}(3e)=1$ this says $P_{3}(t)=1$ for $3\mid t$ and $P_{3}(t)=0$
otherwise.

### 1. Panmagic implies magic

A panmagic square of line sum $t$ is semi-magic and all six broken diagonals sum
to $t$. Two of those broken diagonals are the main ones: reading the indices
modulo three,

$$\texttt{brokenDiagSum}\ M\ 0=\sum_{i}M_{i,\,i+0}=\sum_{i}M_{ii}=\texttt{diagSum}\ M,
\qquad
\texttt{brokenAntiDiagSum}\ M\ 0=\texttt{antiDiagSum}\ M .$$

So such a square is automatically a magic square of line sum $t$.

### 2. The centre identity

For a magic square of order three and line sum $t$, adding the middle row, the
middle column and the two diagonals counts the centre four times and every other
cell once; comparing with four copies of the line sum gives

$$3\,M_{11}=t .$$

This is the formalized lemma `center_of_order_three`. Hence $3\mid t$ is
*necessary* for the existence of a magic square of line sum $t$ — and therefore
also for a panmagic one.

### 3. Conclusion

If $3\nmid t$ then `panMagicSquares 3 t` is empty, so
`panMagicCount 3 t = 0`.

### 4. Formalization notes

* The reduction is done with `Finset.card_eq_zero` and
  `Finset.not_nonempty_iff_eq_empty`, mirroring the existing reduction
  `magic_count_three_otherwise`; the divisibility witness is the centre entry
  `(M 1 1 : ℕ)`.
* The bridge from `IsPanMagic` to `IsMagic` is a `simpa` that rewrites the two
  offset-zero broken diagonals into `diagSum` and `antiDiagSum`; the index
  identity `i + 0 = i` on `Fin 3` is handled by `simp`.
* The statement is deliberately kept as a separate node rather than folded into
  `pan_three_card`, so that the "divisible" and "non-divisible" halves of the
  count can be cited independently — the same shape used for
  `magic_count_three_otherwise` in Mission I.
