For every $n\ge1$, the full target asks for one polynomial $P\in\mathbb Q[X]$ satisfying

$$
\deg P=(n-1)^2,\qquad P(t)=H_n(t)\quad(t\in\mathbb N),
$$

$$
P(-n-t)=(-1)^{n-1}P(t)\quad(t\in\mathbb Z),
\qquad P(-k)=0\quad(1\le k\le n-1).
$$

This reduction connects the three existing milestones without introducing a new mathematical assumption. The existence milestone supplies a polynomial $P$, its exact degree, and its counting identity at every natural line sum. Both the reciprocity milestone and the vanishing milestone are quantified over any polynomial with that counting identity. Apply them to the same polynomial $P$ and combine the resulting conclusions.

The imported children are `MagicSquares.semi_magic_polynomial_exists`, `MagicSquares.semi_magic_reciprocity`, and `MagicSquares.semi_magic_vanishing`. This is a conditional proof of the root from those children, not a direct proof of reciprocity. The reciprocity child remains the unresolved mathematical input; the separate closed-support proofs address existence and vanishing. Their platform verification statuses are recorded independently from this reduction.
