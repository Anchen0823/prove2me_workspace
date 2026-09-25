## Classification of symmetric order-three magic squares

Let $M=(M_{ij})$ be a $3\times3$ array of nonnegative integers which is
**symmetric** ($M_{ij}=M_{ji}$) and **magic** of line sum $3e$. The theorem is
that $M$ is determined by its top-left corner:

$$M=\begin{pmatrix}
a & 2e-a & e\\
2e-a & e & a\\
e & a & 2e-a
\end{pmatrix},\qquad a=M_{00}.$$

### 1. Symmetry removes three conditions

Symmetry identifies $M_{01}=M_{10}$, $M_{02}=M_{20}$ and $M_{12}=M_{21}$. Writing

$$M=\begin{pmatrix} a & b & c\\ b & m & f\\ c & f & i\end{pmatrix},$$

column $j$ is the transpose of row $j$, so the three column conditions coincide
with the three row conditions. There remain five equations in the six unknowns
$a,b,c,m,f,i$:

$$\text{(E1)}\ a+b+c=3e,\quad
\text{(E2)}\ b+m+f=3e,\quad
\text{(E3)}\ c+f+i=3e,$$
$$\text{(E4)}\ a+m+i=3e,\quad
\text{(E5)}\ 2c+m=3e .$$

### 2. Solving

Everything is done in $\mathbb{N}$, where cancellation is available in the
additive form used below and the only subtraction is the truncated one appearing
in the answer.

1. **The corner parameter is a fibre.** Subtracting (E5) from (E4) cancels the
   common term $m$ and gives
   $$a+i=2c .$$
   Subtracting (E5) from (E2) likewise gives $b+f=2c$.
2. **The anti-diagonal forces $c=e$.** Adding (E1) and (E3) gives
   $a+b+2c+f+i=6e$, i.e. $(a+i)+(b+f)+2c=6e$. Substituting the two relations
   above turns this into $2c+2c+2c=6e$, hence $c=e$ and then, from (E5),
   $m=3e-2c=e$.
3. **The rows determine the rest.** With $c=m=e$, equations (E1)--(E3) read
   $$a+b=2e,\qquad b+f=2e,\qquad f+i=2e,$$
   so $f=a$ and then $b=2e-a$, $i=2e-a$.

Putting the pieces together,

$$M=\begin{pmatrix} a & 2e-a & e\\ 2e-a & e & a\\ e & a & 2e-a\end{pmatrix}
=\texttt{symmMagic3}\ e\ a .$$

### 3. Admissibility

The displayed array consists of nonnegative integers for *every* $a$, since its
entries are $a$, $2e-a$ and $e$. Note that $2e-a$ is truncated subtraction, so
the array is genuinely *not* of line sum $3e$ for all $a$: row $0$ sums to
$a+(2e-a)+e$, which equals $3e$ exactly when $a\le 2e$ and exceeds it otherwise.
This is the origin of the parameter interval $\{0,\dots,2e\}$ used by the
companion counting theorem `symm_three_bij`.

### 4. Formalization notes

* The five line equations are extracted with
  `simpa [rowSum, Fin.sum_univ_three] using hM.1.1 (0 : Fin 3)` and its
  analogues, while the three symmetry identities come straight from
  `hsym (0 : Fin 3) (1 : Fin 3)` and so on.
* After `ext i j` and `fin_cases`, each of the nine matrix entries is a ground
  instance and a single `omega` closes it — including the truncated-subtraction
  step $2e-a$. No explicit case split on $a\le 2e$ is required here, because the
  goal is only the *classification*, not admissibility.
* `ext i j` on `Square 3 ℕ` produces equality of natural numbers directly;
  appending `apply Fin.ext` fails afterwards, as there is no `Fin` equality left
  to reduce.
* The shape is packaged in the definition module `MagicSquaresSpecial3` as
  `symmMagic3 e a`, so the counting theorem can refer to it by name.
