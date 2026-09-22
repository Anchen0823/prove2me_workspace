# Weighted Weisner cancellation

For each `y` in the interval `[a,b]`, group the weight of every `c` with
`d <= c <= b` by the value `c ⊔ a = y`.  Call that grouped weight `fibre(y)`.
Summing `fibre(y)` over `a <= y <= x` counts exactly the weights with
`d <= c <= x`: the implication `c ⊔ a <= x` gives `c <= x`, while conversely
`c <= x` and `a <= x` give `c ⊔ a <= x`.  The prefix hypothesis therefore
makes every such fibre-prefix sum zero.

Strong induction on the finite strict order of the interval now isolates the
top fibre.  All terms strictly below `x` vanish by the induction hypothesis,
so the zero prefix sum at `x` forces `fibre(x)=0`.  Taking `x=b` gives the
claimed join-fibre sum.

This is a proved weighted generalization whose cancellation mechanism matches
the order-dual viewpoint behind Weisner's theorem.  It is not quoted as a
verbatim result from Stanley.  The only external reference is Richard Stanley,
[*Enumerative Combinatorics*, Volume 1, Corollary 3.9.3, p. 313](https://math.mit.edu/~rstan/ec/ec1.pdf),
applied in the order dual.
