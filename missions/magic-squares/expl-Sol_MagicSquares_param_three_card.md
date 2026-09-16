## Counting the MacMahon parameter pairs: $\mathrm{paramCount}(e) = 2e^{2} + 2e + 1$

Recall

$$\mathrm{paramSet}(e)=\\{(a,c)\in\mathbb{N}^{2} : e \le a+c \le 3e,\\; a \le e+c,\\; c \le e+a\\},$$

which by the reduction `magic_three_param_bij` indexes exactly the $3\times 3$
magic squares with nonnegative entries and line sum $3e$.

### 1. Fibre decomposition

The four inequalities force $a \le 2e$ and $c \le 2e$ (add $a+c \le 3e$ to
$a \le e+c$ to get $2a \le 4e$, and symmetrically), so filtering the box
$[0,2e]^{2}$ is lossless. Fix $a \in [0, 2e]$ and solve for $c$:

* $e \le a + c \iff c \ge e - a$;
* $a \le e + c \iff c \ge a - e$;
* $c \le e + a$ and $a + c \le 3e \iff c \le \min(e+a,\\, 3e-a)$.

Hence the admissible $c$ are exactly the integers in the interval
$[\,\mathrm{paramLo}(e,a),\\, \mathrm{paramHi}(e,a)\,]$ with

$$\mathrm{paramLo}(e,a)=\begin{cases}e-a & a\le e\\\\ a-e & a>e\end{cases},
\qquad
\mathrm{paramHi}(e,a)=\begin{cases}e+a & a\le e\\\\ 3e-a & a>e\end{cases}.$$

(The two "lower" bounds combine to $|a-e|$; the two "upper" bounds combine to
$e+a$ resp. $3e-a$, the smaller of which switches at $a=e$.) So

$$\mathrm{paramSet}(e) \;\cong\; \coprod_{a=0}^{2e} \\{\mathrm{paramLo}(e,a),\dots,\mathrm{paramHi}(e,a)\\},$$

and this bijection is what the formal proof establishes with `Finset.card_bij`
against an explicit `Finset.sigma`.

### 2. Widths

$$\mathrm{paramWidth}(e,a) = \mathrm{paramHi} - \mathrm{paramLo} + 1 =
\begin{cases} 2a + 1 & a \le e,\\\\ 4e - 2a + 1 & a > e.\end{cases}$$

By `Finset.card_sigma`,
$\mathrm{paramCount}(e) = \sum_{a=0}^{2e} \mathrm{paramWidth}(e,a)$.

### 3. Summation

Split at $a = e$ (i.e. $a = 0,\dots,e$ and $a = e+1,\dots,2e$):

* **Increasing block.** $\sum_{a=0}^{e}(2a+1) = (e+1)^{2}$ — the classical
  identity that the first $n$ odd numbers sum to $n^{2}$.
* **Decreasing block.** Writing $a = e+1+b$ with $b = 0,\dots,e-1$,
  $\mathrm{paramWidth} = 4e - 2(e+1+b) + 1 = 2e - 2b - 1$, i.e. the odd numbers
  $2e-1, 2e-3, \dots, 1$ in reverse. Under the reflection $b \mapsto e-1-b$ this
  is the same as the increasing block, hence sums to $e^{2}$.

Therefore

$$\mathrm{paramCount}(e) = (e+1)^{2} + e^{2} = 2e^{2} + 2e + 1,$$

which is MacMahon's formula.

### 4. Formalization notes

* The interval endpoints are truncated subtractions on $\mathbb{N}$, so the
  natural encoding is `if a ≤ e then e - a else a - e`; every arithmetic step is
  discharged by `omega` after a case split on `a ≤ e`.
* The reflected sum uses `Finset.sum_range_reflect`, avoiding any manual
  reindexing.
* The fibres are pairwise disjoint by construction (`Finset.sigma`), so no
  overcounting correction is needed — unlike the naive
  "$(e+1)^2 + (e+1)^2 - (2e+1)$" version, which counts $a=e$ twice.
