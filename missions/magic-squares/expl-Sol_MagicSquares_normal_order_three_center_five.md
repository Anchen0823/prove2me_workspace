## The centre of a normal $3 \times 3$ magic square is $5$

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

`omega` combines the two linear constraints and concludes $M_{11} = 5$.