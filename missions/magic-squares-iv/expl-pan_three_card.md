## The panmagic squares of order three: $P_{3}(3e) = 1$

A $3\times3$ array of nonnegative integers is **panmagic** (pandiagonal) of line
sum $s$ when all three rows, all three columns and all six broken diagonals sum
to $s$. Write $P_{n}(t)$ for the number of such squares of order $n$ and line
sum $t$. The theorem is

$$P_{3}(3e)=1\qquad\text{for every }e\in\mathbb{N}.$$

### 1. The twelve line equations

Write the array as

$$M=\begin{pmatrix} a & b & c\\ d & m & f\\ g & h & i\end{pmatrix},$$

and let all twelve line sums equal $3e$. The six broken diagonals are

| offset | descending | ascending |
|---|---|---|
| $0$ | $a+m+i$ | $c+m+g$ |
| $1$ | $b+f+g$ | $a+f+h$ |
| $2$ | $c+d+h$ | $b+d+i$ |

Together with the three rows and the three columns this is a system of twelve
linear equations in the nine entries.

### 2. The system has a unique nonnegative solution

* $a+m+i=3e$ and $c+m+g=3e$ give $a+i=c+g$; $b+f+g=3e$ and $b+d+i=3e$ give
  $f+g=d+i$.
* The middle row $d+m+f=3e$ and the middle column $b+m+h=3e$, combined with the
  diagonal identities above, force $d=m=f$.
* Substituting back, the middle row reads $3m=3e$, so $m=e$ (the nonnegative
  integers are an integral domain).
* Then $c+d+h=3e$ and $m=e$, $d=e$ give $c+h=2e$; similarly $a+i=2e$,
  $b+g=2e$, $c+g=2e$, $a+g=2e$, $b+h=2e$. From $b+g=2e=c+g$ we get $b=c$, and
  from $a+g=2e=b+g$ we get $a=b$.
* Finally the top row $a+b+c=3e$ becomes $3a=3e$, so $a=e$; and then
  $g=2e-a=e$, $h=2e-b=e$, $i=2e-a=e$, $d=f=e$.

So every entry equals $e$, i.e. $M=\texttt{constSquare3}\ e$.

### 3. Conversely

The constant array with all entries $e$ has every row, column and broken diagonal
sum equal to $3e$, and all its entries lie in $\{0,\dots,3e\}$, so it is read
over `Fin (3*e+1)` and is a genuine element of the filtered finset. Hence the
finset is the singleton $\{\texttt{constSquare3}\ e\}$ and its cardinality is $1$.

### 4. Formalization notes

* The argument is *subtraction-free*: all twelve hypotheses are of the form
  "a sum of three entries equals $3e$", so the entire uniqueness step is a single
  `omega` call. No case analysis on truncated subtraction is needed — in
  contrast with the symmetric case, where the *shape* of the solution depends on
  the boundary $a\le 2e$.
* Uniqueness of the element is proved with `Finset.eq_singleton_iff_unique_mem`
  (membership of the constant square plus "every member equals it"), which is
  cheaper than exhibiting a bijection to a one-element type.
* The broken diagonals are expanded with `Fin.sum_univ_three` after `fin_cases`
  on the offset `k : Fin 3`; the indices `i + k` and `Fin.rev i + k` are
  reduced by `simp` in `Fin 3`.
