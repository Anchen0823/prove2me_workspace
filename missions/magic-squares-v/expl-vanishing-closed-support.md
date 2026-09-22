Let $n\ge1$ and let $P\in\mathbb Q[X]$ agree with the semi-magic counting function at every nonnegative integer. Then

$$
P(-k)=0\qquad(1\le k\le n-1).
$$

The proof uses disjoint permutation matrices and the closed-support boundary recurrence. It does not assume Ehrhart-Macdonald reciprocity.

For a board $B$ containing a permutation support, write $P_B$ for the polynomial counting matrices supported inside $B$, including at line sum zero. For boards containing no permutation support, set $P_B=0$; this convention agrees with their counts at every positive line sum. The closed-support polynomiality proof is included in the source.

For any permutation support $\phi\subseteq B$, subtracting that permutation matrix and applying inclusion-exclusion to the zero cells on $\phi$ gives, at nonnegative integer $x$,

$$
P_B(x+1)=P_B(x)+
\sum_{\varnothing\ne S\subseteq\phi}(-1)^{|S|+1}P_{B\setminus S}(x+1).
$$

Both sides are polynomials; their agreement at infinitely many integers makes this identity valid for every rational $x$. For every admissible board, $P_B(0)=1$.

We prove a stronger board statement: if $B$ contains $k+1$ pairwise disjoint permutation supports, where $k\ge1$, then $P_B(-k)=0$. Choose one of those supports as $\phi$. Removing any subset of its cells leaves the other $k$ permutation supports untouched.

For $k=1$, evaluate the recurrence at $x=-1$. Each smaller board still contains a permutation, so every polynomial on the right is evaluated to one at zero. Since $\phi$ is nonempty,

$$
\sum_{\varnothing\ne S\subseteq\phi}(-1)^{|S|+1}=1.
$$

Consequently $1=P_B(-1)+1$, proving the first zero.

For $k>1$, induction gives $P_{B\setminus S}(-(k-1))=0$ for all the smaller boards, since each retains $k$ disjoint permutations. It also gives $P_B(-(k-1))=0$, by retaining any $k$ of the original $k+1$ permutations. The recurrence at $x=-k$ now forces $P_B(-k)=0$.

The full $n\times n$ board contains $n$ pairwise disjoint permutation supports: use the cyclic shifts $i\mapsto i+a$ on $\mathbb Z/n\mathbb Z$. Thus the board statement applies for every $k$ from one to $n-1$. Finally, the given polynomial $P$ and the full-board polynomial agree at every natural number, so polynomial uniqueness identifies them. The case $n=1$ has an empty vanishing range.

`ClosedEvaluation` extends the boundary recurrence to rational arguments and establishes the value at zero. `ClosedVanishing` proves the induction on the number of disjoint permutations, and `CyclicPermutations` supplies those permutations on the full board. No reciprocity result or unproved theorem is imported.
