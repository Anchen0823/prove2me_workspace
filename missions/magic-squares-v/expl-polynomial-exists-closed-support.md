For every $n\ge1$, the semi-magic counting function is a rational polynomial of exact degree $(n-1)^2$ on **all** nonnegative integer line sums:

$$
\exists P\in\mathbb Q[X],\qquad \deg P=(n-1)^2,
\qquad P(t)=H_n(t)\quad(t\in\mathbb N).
$$

The proof combines the positive-line-sum polynomial and its degree bounds with a closed-support induction that retains the value at zero. This additional induction avoids using Ehrhart reciprocity or a face-lattice Euler formula.

Let $F_B(t)$ count matrices with line sum $t$ whose support is contained in a fixed board $B$. If $B$ contains no permutation support, Hall's theorem shows that $F_B(t)=0$ for every positive $t$. Such a board still has the zero matrix at level zero, and the argument never treats its entire counting function as the zero polynomial.

If $B$ contains a permutation support $\phi$, subtract its permutation matrix from the matrices positive on every cell of $\phi$. This gives a bijection with all matrices counted by $F_B(t)$, starting from level $t+1$. The other matrices have a zero in some cell of $\phi$. Applying inclusion-exclusion to these zero-cell conditions yields

$$
F_B(t+1)-F_B(t)=
\sum_{\varnothing\ne S\subseteq\phi}
(-1)^{|S|+1}F_{B\setminus S}(t+1).
$$

Every board on the right is strictly smaller. Induct on the board's cardinality. A smaller board containing a permutation supplies a polynomial by induction; one containing none contributes zero because its argument is $t+1>0$. Thus the forward difference is polynomial. Discrete antidifferentiation, initialized at the actual value $F_B(0)$, makes $F_B$ polynomial on all of $\mathbb N$. The full board contains the identity permutation and has $F_B(t)=H_n(t)$.

For completeness, the positive-level degree argument is included in the same proof source. Exact-support recurrences give polynomiality, and the dimension of the zero-line-sum space bounds the degree above by $(n-1)^2$. For the lower bound, an explicit family of matrices with $(n-1)^2$ independently varying entries forces growth of that order, hence a polynomial degree at least $(n-1)^2$. The positive-level polynomial and the newly obtained all-level polynomial agree at every positive integer, so they are equal. This transfers the exact degree to the all-level polynomial.

`ClosedSupport` proves the subtraction bijection and the Hall-based emptiness statement. `ClosedSupportIE` is the finite inclusion-exclusion identity. `PolynomialRecurrence` supplies strict-board induction and discrete summation, and `ClosedPolynomial` specializes them to semi-magic matrices. `S5Bridge` connects polynomial uniqueness to the existing degree proof. No reciprocity or negative-integer vanishing result is assumed or asserted.
