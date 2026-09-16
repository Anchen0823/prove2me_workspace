## Stars and bars: $\#\{x\in\mathbb{N}^{k+1}:\sum x_{i}=n\}=\binom{n+k}{n}$

### 1. Why a box is needed

$\mathbb{N}^{k+1}$ has no `Fintype`, so the count is taken inside a fixed box:
`comps N (k+1) n` is the set of functions $\mathrm{Fin}(k+1)\to\mathrm{Fin}(N+1)$
whose values sum to $n$. The hypothesis $n\le N$ makes the box **inactive** —
every coordinate of such a tuple is at most $n$, hence at most $N$ — so the
boxed count is the honest count. Keeping $N$ fixed while $k$ and $n$ vary is
also what makes the induction below avoid any reindexing of the tail.

### 2. Splitting off the first coordinate

The map $x\mapsto(x_{0},\,x_{1},\dots,x_{k})$ identifies compositions of $n$
into $k+2$ parts with the disjoint union, over $i=0,\dots,n$, of the
compositions of $n-i$ into $k+1$ parts. In Lean this is a `Finset.card_bij`
onto an explicit `Finset.sigma`; because the fibres all have the same carrier
type `Fin k → Fin (N+1)`, the sigma is really a product and both injectivity
and surjectivity reduce to `Fin.cons_self_tail` / `Fin.tail_cons`.

### 3. The recurrence and hockey-stick

Writing $c(k,n)$ for the count, the split gives
$$c(k+1,n)=\sum_{i=0}^{n}c(k,n-i),\qquad c(0,n)=[n=0].$$
The binomial $\binom{n+k}{n}$ satisfies the same recurrence, by the
hockey-stick identity
$$\sum_{j=0}^{n}\binom{j+k}{j}=\binom{n+k+1}{n},$$
which is one induction from Pascal's rule
$\binom{a+1}{b+1}=\binom{a}{b}+\binom{a}{b+1}$. Reindexing $i\mapsto n-i$ in
the recurrence is exactly `Finset.sum_range_reflect`, so no manual reindexing
is needed.

### 4. Formalization notes

* The statement is phrased with $k+1$ parts (rather than $k$) so that the
  formula $\binom{n+k}{n}$ never involves a truncated subtraction; had it been
  phrased with $k$ parts the case $k=0$ would need the convention
  $\binom{n-1}{n}$, which in $\mathbb{N}$ is not uniformly correct.
* `Fin.cons` is the dependent version, so its type family has to be pinned
  explicitly (`α := fun _ => Fin (N+1)`); otherwise higher-order unification
  leaves the family as a metavariable and the coercion to $\mathbb{N}$ fails.
* The base case $k=0$ is a singleton extent: compositions of $n$ into one part
  form $\{\,(\,n\,)\,\}$, and the box hypothesis $n\le N$ is exactly what makes
  that element exist.
