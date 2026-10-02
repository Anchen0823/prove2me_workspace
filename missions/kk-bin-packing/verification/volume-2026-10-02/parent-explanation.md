For an instance $I$ with item sizes in $(0,1)$, this reduction establishes the implication from the two stated core lemmas to

$$SIZE(I)\le LIN(I)\le OPT(I)\le LIN(I)+\frac{m(I)+1}{2}.$$

The first two inequalities use the volume and LP lower bounds. For the last inequality, the remaining assumptions are: existence of feasible configuration vectors arbitrarily close to the LP infimum with support size at most $m(I)$, and the floor-rounding certificate for every feasible vector. Neither core lemma is proved by this submission.

Fix a positive tolerance and such a sparse vector $x$. Write $s$ for its support size, $N$ for the sum of its integer parts, and $R$ for the residual multiset. The certificate supplies a packing $P$ of the removed items and bounds

$$|P|\le N,\qquad SIZE(R)\le lpCost(x)-N,\qquad OPT(R)\le s.$$

Because multiset subtraction truncates counts, this includes LP solutions that over-cover the input: the bins of $P$ contain only retained original items. The independently proved elementary bound also gives

$$OPT(R)\le 2SIZE(R)+1.$$

Averaging these two bounds yields

$$OPT(R)\le SIZE(R)+\frac{s+1}{2}.$$

An optimal residual packing exists since a singleton packing is feasible and the costs are natural numbers. Joining it to $P$ therefore gives

$$OPT(I)\le lpCost(x)+\frac{s+1}{2}<LIN(I)+\varepsilon+\frac{m(I)+1}{2}.$$

If the exact upper bound failed, choose the positive tolerance to be half the gap, obtaining a contradiction. Thus no separate assumption that the real LP infimum is attained is needed in this reduction.

This follows the principal/residual construction of Karmarkar–Karp, FOCS 1982, p. 313, Lemma 2, while isolating its finite-LP sparsity and combinatorial rounding obligations as explicit reusable children.
