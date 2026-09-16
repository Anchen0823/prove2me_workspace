## Reduction: MacMahon's count $M_{3}(3e) = 2e^{2} + 2e + 1$

The parent theorem is decomposed into two independent children.

**(1) `magic_three_param_bij` — parametrization.**
Let $M$ be a $3 \times 3$ magic square with nonnegative entries and line sum
$3e$. MacMahon's centre identity gives $M_{11} = e$. Putting $a = M_{00}$ and
$c = M_{02}$, the eight line identities determine every remaining cell:

$$M=\begin{pmatrix} a & 3e-a-c & c \\ e+c-a & e & e+a-c \\ 2e-c & a+c-e & 2e-a\end{pmatrix}.$$

Indeed $M_{22} = 2e-a$ and $M_{20} = 2e-c$ come from the two diagonals, then
$M_{01} = 3e-a-c$ and $M_{21} = a+c-e$ from the outer rows/columns, and
$M_{10} = e+c-a$, $M_{12} = e+a-c$ from the remaining ones. Hence $M \mapsto (a,c)$
is injective, and the nine entries are nonnegative exactly when
$$e \le a+c \le 3e,\qquad a \le e+c,\qquad c \le e+a .$$
Conversely every pair satisfying these inequalities produces via the display a
valid magic square, so the map is a bijection and
$M_{3}(3e) = \mathrm{paramCount}(e)$.

**(2) `param_three_card` — counting the parameters.**
Substituting $p = a-e$ and $q = c-e$, the four inequalities become $|p+q| \le e$
and $|p-q| \le e$; since $\max(|p+q|,|p-q|) = |p| + |q|$, this is precisely
$|p| + |q| \le e$, the $\ell_{1}$ ball of radius $e$ in $\mathbb{Z}^{2}$. Its
sphere $|p| + |q| = k$ carries $4k$ lattice points for $k \ge 1$ and one for
$k = 0$, so the ball has
$$1 + 4\sum_{k=1}^{e} k = 1 + 2e(e+1) = 2e^{2} + 2e + 1$$
points, i.e. $\mathrm{paramCount}(e) = 2e^{2} + 2e + 1$.

### Status

This submission is a **reduction**, not a direct proof: both children are
currently Open platform theorems. The parent resolves to Proved as soon as both
children are proved. The reduction body itself is `sorry`-free:

```lean
theorem solution (e : ℕ) : magicCount 3 (3 * e) = 2 * e ^ 2 + 2 * e + 1 := by
  rw [magic_three_param_bij e, param_three_card e]
```