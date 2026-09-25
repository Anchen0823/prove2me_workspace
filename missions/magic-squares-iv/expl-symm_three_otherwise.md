## No symmetric magic squares of order three when $3\nmid t$

Let $S_{n}(t)$ be the number of symmetric magic squares of order $n$ and line sum
$t$. The theorem is the vanishing half of the order-three count:

$$3\nmid t\ \Longrightarrow\ S_{3}(t)=0 .$$

Together with $S_{3}(3e)=2e+1$ this says $S_{3}(t)=2(t/3)+1$ for $3\mid t$ and
$S_{3}(t)=0$ otherwise.

### 1. Symmetry does not relax the obstruction

A symmetric magic square of order three and line sum $t$ is in particular a magic
square of order three and line sum $t$: the filtering predicate of
`symmetricMagicSquares` is exactly `IsMagic … t ∧ IsSymmetric …`.

### 2. The centre identity

For any magic square of order three, the middle row, the middle column and the
two diagonals together count the centre four times and each other cell once, so

$$3\,M_{11}=t .$$

This is `center_of_order_three`. In particular $3\mid t$ is necessary for
existence.

### 3. Conclusion

If $3\nmid t$ then `symmetricMagicSquares 3 t` is empty, hence
`symmetricMagicCount 3 t = 0`.

### 4. Formalization notes

* The proof is the symmagic analogue of `magic_count_three_otherwise`, with one
  extra projection: the membership hypothesis must first be split into the magic
  and the symmetry halves, because the filtering predicate is a conjunction.
* The divisibility witness is again the centre entry `(M 1 1 : ℕ)`.
* Keeping this as its own node mirrors the structure of the panmagic case and
  makes the two "non-divisible" facts independently citable in the goal
  `special_three_count`.
