Let $k\ge2$ be an integer, let $0<g\le1/2$, and let the input instance satisfy $SIZE(I)\ge1$. For every output packing $P$ of ALGORITHM 2, this reduction establishes its validity and the bound

$$|P|\le\max\left\{(1+2g)OPT(I)+1,\quad OPT(I)+\left(1+\frac{\log SIZE(I)}{\log k}\right)\left(1+4k+2k\log(1/g)\right)+2+\frac{2\log(1/g)}{1-1/k}\right\}.$$

The argument combines the existing milestones for the Step 3 packing, LP cost telescoping, the iteration count, geometric grouping, and the insertion of small items. It additionally imports the separately proved inequality `lin_le_opt`. The recurrence behind the iteration count, the LP telescoping milestone, and the geometric-grouping milestone remain assumptions of the reduction.

Write $A$ for the instance left after removing the items of size at most $g$, and $P_0$ for all bins present after Step 3. The Step 3 milestone asserts that $P_0$ packs $A$ and that

$$|P_0|\le\sum_{i<t}X_i+2kt\left(2+\log(1/g)\right)+2+\frac{2\log(1/g)}{1-1/k}.$$

Induction over the insertion process proves that inserting the removed items preserves item counts and the unit-capacity condition. The two complementary parts of $I$ therefore yield a valid final packing of the whole input. Lemma 3, applied with parameter $2g$, gives

$$|P|\le\max\{|P_0|,(1+2g)OPT(I)+1\}.$$

If the loop executes no iterations, the sum of principal bins and the iteration charge both vanish. All additional terms in the claimed upper bound are nonnegative, so the result follows directly from the Step 3 estimate. This case does not require taking the logarithm of the potentially empty instance $A$.

Suppose instead that at least one iteration executes. Its initial loop condition shows that $SIZE(A)>0$, so $A$ is nonempty. Geometric grouping and the LP lower bound give

$$LIN(\operatorname{geomJ}_k(A))\le LIN(A)\le OPT(A)\le OPT(I).$$

For the final inequality, take an optimal packing of $I$ and filter every bin to retain just the items in $A$. Since all item sizes are nonnegative, every filtered bin remains feasible, and the number of bins is unchanged. An optimal integral packing exists because singleton bins give a feasible packing and the costs are natural numbers.

The telescoping milestone now gives

$$\sum_{i<t}X_i\le OPT(I)+t.$$

The iteration milestone, together with the monotonicity of the sum and the logarithm, gives

$$t\le1+\frac{\log SIZE(A)}{\log k}\le1+\frac{\log SIZE(I)}{\log k}.$$

Substituting these estimates into the Step 3 bound and collecting the coefficient of $t$ yields

$$1+2k(2+\log(1/g))=1+4k+2k\log(1/g).$$

This coefficient is nonnegative. The resulting bound on $|P_0|$ is precisely the second branch of the claimed maximum. Combining it with the small-item insertion estimate completes the reduction.

The proof follows the final ALGORITHM 2 estimate in Karmarkar–Karp (FOCS 1982), p. 317. It does not import the target theorem itself.
