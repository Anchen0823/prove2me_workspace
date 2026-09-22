# Closed-support induction for the missing zero value

Date: 2026-09-20. The main argument targets `semi_magic_polynomial_exists`.
Its extension below also establishes the negative-integer vanishing theorem.
Reciprocity remains unresolved.
See the dated verification record for compilation and platform acceptance.

## Change of counting function

For a board of permitted cells $B\subseteq [n]\times[n]$, let $F_B(t)$ count
nonnegative integral matrices with every row and column summing to $t$ and
support **contained in** $B$. In particular, $F_B(0)=1$ for every board.
The previous functions counted matrices whose support was **equal to** $B$.
Their positive-level polynomials remain useful, but extrapolating them to zero
is not necessary to prove polynomiality of $F_B$.

Call a board admissible when it contains the support of a permutation matrix.
Hall's theorem implies that a non-admissible board has $F_B(t)=0$ for every
$t\ge1$. Its value at zero is still one; consequently it must not be assigned
the zero polynomial on all of the natural numbers.

## The boundary recurrence

Fix an admissible board and a permutation support $\phi\subseteq B$.
Subtracting the permutation matrix bijects matrices counted by $F_B(t+1)$
which are positive on all cells of $\phi$ with matrices counted by $F_B(t)$.
The inverse adds the permutation matrix. Nonnegativity and every line sum
are preserved with the indicated shift; both directions keep support in $B$.

The remaining matrices have a zero in at least one cell of $\phi$.
Inclusion-exclusion over these zero-cell conditions gives

$$
F_B(t+1)-F_B(t)=
\sum_{\varnothing\ne S\subseteq\phi}
(-1)^{|S|+1} F_{B\setminus S}(t+1),\qquad t\ge0.
$$

Every board on the right is a strict subset of $B$. Crucially its argument is
$t+1$, which is always positive. A non-admissible smaller board therefore
contributes zero here, even when $t=0$.

## Induction and discrete summation

Induct on the number of cells of an admissible board. For each admissible
smaller board, use its counting polynomial supplied by induction. For each
non-admissible smaller board, use the zero polynomial **only at the positive
arguments appearing on the right**. The resulting alternating sum is a
polynomial $R_B$ and

$$
F_B(t+1)=F_B(t)+R_B(t+1).
$$

Discrete polynomial antidifferentiation now gives

$$
F_B(t)=F_B(0)+\sum_{j=0}^{t-1}R_B(j+1),
$$

a rational polynomial for every natural $t$, including zero. The full board
is admissible (it contains the identity permutation), and its closed-support
count is exactly $H_n(t)$. This proves the all-natural-number polynomial
existence statement without an Euler-characteristic theorem, triangulation,
or Ehrhart reciprocity.

The earlier positive-level polynomial already has degree exactly $(n-1)^2$
for $n\ge1$. The new polynomial agrees with it at every positive integer;
polynomial uniqueness transfers the exact degree. In the implementation,
`S5Bridge` expresses this uniqueness through `qAll` and the equivalent identity
$\sum_B s_B=1$.

## Edge cases and logical scope

- For $n=0$, the empty permutation has empty support, the boundary sum is
  empty, and the unique empty matrix is counted at every level. The general
  polynomiality lemma therefore also holds at order zero. The mission's
  exact-degree theorem retains its required hypothesis $n\ge1$.
- A board containing a permutation may also contain unusable cells. No step
  assumes it is the exact support of a positive matrix.
- For a board which is a single permutation support, every smaller board in
  the boundary sum is non-admissible, so the recurrence yields the constant one.
- This proves the **sum** $\sum_B s_B=1$. It does not prove the individual
  support-sign identity or the face-lattice Euler identity from `S5-NOTES.md`.
  Those were sufficient inputs, not individually necessary prerequisites.

## Formal components

| File | Role |
| --- | --- |
| `ClosedSupport.lean` | Closed fibres, permutation subtraction bijection, Hall emptiness |
| `ClosedSupportIE.lean` | Generic finite inclusion-exclusion for forbidden cells |
| `PolynomialRecurrence.lean` | Abstract strict-board induction and discrete antiderivative |
| `ClosedPolynomial.lean` | Boundary recurrence, full-board specialization, exact-degree result |
| `S5Bridge.lean` | Polynomial uniqueness and connection to the earlier zero-value obstruction |

All files are under `examples/magic-squares/spencer/`. The prior degree proof
continues to supply the sharp upper and lower bounds. The boundary recurrence
is a new argument developed in this continuation; it should not be described
as a verbatim translation of Spencer's paper.

## Extension: the entire vanishing list

`ClosedEvaluation.lean` turns the boundary recurrence into a polynomial identity,
valid at every rational argument. `ClosedVanishing.lean` then proves that a board
containing $k+1$ disjoint permutation supports has $P_B(-k)=0$ for $k\ge1$.
Remove cells from one chosen permutation; the other $k$ survive in every child.
For $k=1$, evaluate at $-1$ and use the alternating subset sum equal to one.
For larger $k$, both the parent at $-(k-1)$ and all children at $-(k-1)$ vanish
by induction, forcing the next zero. The $n$ cyclic shifts supplied by
`CyclicPermutations.lean` give all roots $-1,\ldots,-(n-1)$ on the full board.

The complete mathematical explanation is in
[expl-vanishing-closed-support.md](expl-vanishing-closed-support.md).
Both the all-level polynomial theorem and this vanishing theorem passed the
pinned `SpencerRoute` build; consult verification records for the independent
standalone builds, axiom checks, and server verdicts.
