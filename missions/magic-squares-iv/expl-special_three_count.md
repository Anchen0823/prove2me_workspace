## The complete count of the special order-three magic squares

Let $P_{3}(t)$ be the number of panmagic squares of order three and line sum
$t$, and $S_{3}(t)$ the number of symmetric magic squares of order three and line
sum $t$. Both are counted by a single closed form:

$$P_{3}(t)=\begin{cases}1,&3\mid t\\ 0,&3\nmid t\end{cases},
\qquad
S_{3}(t)=\begin{cases}\dfrac{2t}{3}+1,&3\mid t\\[2mm] 0,&3\nmid t\end{cases}.$$

### 1. The divisibility split

Everything hinges on whether $3\mid t$. The obstruction is the order-three
centre identity: for a magic square of line sum $t$ the centre entry satisfies
$3c=t$, so $3\mid t$ is necessary, and both special classes consist of magic
squares. Accordingly the proof branches on `3 ∣ t`.

### 2. The non-divisible branch

For `¬ 3 ∣ t`, both filtered finsets are empty, by
`pan_three_otherwise` and `symm_three_otherwise`; each of those reduces to the
centre identity `center_of_order_three` through `Finset.card_eq_zero`. So both
`if`-expressions evaluate to $0$ and the two conjuncts hold trivially.

### 3. The divisible branch

Write $t=3e$. Then

* **Panmagic.** `pan_three_card` shows that the only panmagic square of line sum
  $3e$ is the constant square, so $P_{3}(3e)=1$.
* **Symmetric.** `symm_three_bij` identifies the symmetric magic squares of line
  sum $3e$ with the admissible corner parameters
  `symmParamSet e = {0, 1, …, 2e}`, so
  $$S_{3}(3e)=\#\{0,\dots,2e\}=2e+1,\qquad\text{i.e.}\qquad S_{3}(3e)=\frac{2t}{3}+1 .$$
  The substitution $t=3e$ in the right-hand side uses $(3e)/3=e$.

### 4. Why the answer is what it is

The two special classes are degenerate in opposite directions, and this is the
substance of the theorem rather than a computational accident:

* **Panmagic.** The six broken diagonals impose six further line conditions on
  top of the eight of a magic square. For order three this collapses the whole
  two-parameter MacMahon family ($M_{3}(3e)=2e^{2}+2e+1$ squares) onto a single
  point — the constant array.
* **Symmetric.** Transposition removes only three of the eight conditions,
  leaving a genuine one-parameter family
  $$\begin{pmatrix} a & 2e-a & e\\ 2e-a & e & a\\ e & a & 2e-a\end{pmatrix},
  \qquad a=0,\dots,2e,$$
  and hence a *linear* count.

So order three exhibits quadratic (magic), linear (symmetric) and constant
(panmagic) behaviour in the same line-sum parameter — a contrast that disappears
at order four, where no closed form is known.

### 5. Formalization notes

* The submission imports the four child modules
  `Theorems.Thm_MagicSquares_{pan_three_card, symm_three_bij, pan_three_otherwise, symm_three_otherwise}`,
  each of which is a `Proved` platform node.
* The divisible branch uses `obtain ⟨e, rfl⟩ := h` to substitute $t=3e$, then
  `simp only [dvd_mul_right, if_true, h3]` to reduce both `if`-expressions; the
  final cardinality step is `rw [symm_three_bij, symmParamCount, symmParamSet,
  Finset.card_range]`.
* The only arithmetic subtlety is $(3e)/3=e$: `Nat.mul_div_left` is stated with
  the divisor implicit and in the orientation $m\cdot n/n=m$, so the proof first
  rewrites with `mul_comm 3 e` and then applies
  `Nat.mul_div_left e (n := 3)`; leaving the divisor implicit makes `norm_num`
  run before the metavariable is assigned.
* The reduction is *complete*, not a sketch: all four children were proved and
  accepted on the platform before this submission.
