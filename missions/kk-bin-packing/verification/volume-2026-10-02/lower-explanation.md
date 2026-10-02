For every finite instance whose item sizes lie in $(0,1)$,

$$SIZE(I)\le LIN(I).$$

The proof uses the item sizes as weights on the demand constraints. Each configuration has total size at most one, so the weighted amount covered by one unit of configuration weight is at most one.

Let $T$ be the finite set of sizes occurring in $I$, let $b_t$ be the multiplicity of size $t$, and let $a_{tc}$ be its multiplicity in configuration $c$. For any feasible nonnegative vector $x$, the demand constraints imply

$$\begin{aligned}
SIZE(I)&=\sum_{t\in T}t b_t\\
&\le\sum_{t\in T}t\sum_{c\in\operatorname{supp}(x)}x_c a_{tc}\\
&=\sum_{c\in\operatorname{supp}(x)}x_c\sum_{t\in T}t a_{tc}\\
&\le\sum_{c\in\operatorname{supp}(x)}x_c.
\end{aligned}$$

The first inequality uses positivity of item sizes. The equality interchanges two finite sums. The final inequality uses nonnegativity of the configuration weights and the unit-capacity condition on every supported configuration.

To pass to the infimum, the feasible-cost set must be nonempty. Packing each item alone supplies a feasible integer configuration vector; for the empty instance this is the zero vector. Thus the total size is a lower bound on a nonempty set of feasible costs, and is at most its infimum, which is $LIN(I)$.

This formalizes the size-weighted argument in Karmarkar–Karp, FOCS 1982, p. 313, Lemma 2. The direct Lean proof uses the instance and configuration-LP definitions and no imported platform theorem assumptions.
