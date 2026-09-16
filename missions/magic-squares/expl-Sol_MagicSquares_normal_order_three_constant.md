## The magic constant of a normal $3 \times 3$ magic square is $15$

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
resulting linear Presburger goal over $\mathbb{N}$.