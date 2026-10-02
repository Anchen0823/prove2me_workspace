For each executed iteration of Algorithm 2, let $I_i$ be the current instance, $J_i$ its rounded part, and $X_i$ the sum of the integer parts of the configuration weights. The reduction proves

$$LIN(I_{i+1})\le LIN(J_i)+1-X_i\le LIN(I_i)+1-X_i,$$

and consequently

$$\sum_{i=0}^{t-1}X_i\le LIN(J_0)+t.$$

Two analytic results are hypotheses of this reduction: `alg2_size_recursion` bounds the residual fractional optimum by the sum of the fractional parts of the current weights, and `geomGroup_bounds` supplies $LIN(J_i)\le LIN(I_i)$. Both are existing milestones; neither is proved here.

The structural conditions needed to apply these results follow directly from the trace. Geometric grouping partitions the original items into the real components of its rounded pairs and the discarded part. Thus every residual instance is a subinstance of the preceding instance and retains item sizes in $(0,1)$. If $g>1$, the initial filtering removes every item, and the residual recurrence keeps every state empty. A positive iteration count would then make the loop-entry and loop-exit inequalities contradict one another. Hence every executed iteration has $g\le1$. Its threshold is at least one, so its current instance is nonempty.

The residual bound and the trace's near-optimality condition give

$$LIN(I_{i+1})\le\sum_c(x_{ic}-\lfloor x_{ic}\rfloor)=lpCost(x_i)-X_i\le LIN(J_i)+1-X_i.$$

The grouping comparison gives the second inequality. To sum the bounds while keeping the sharper initial value, use the first inequality for iteration zero and both inequalities for each later iteration. Induction yields, for $1\le n\le t$,

$$\sum_{i=0}^{n-1}X_i+LIN(I_n)\le LIN(J_0)+n.$$

All feasible LP costs are nonnegative, so their real infimum is nonnegative. Dropping $LIN(I_t)$ proves the desired sum bound. When $t=0$, the sum is empty and the same nonnegativity proves the conclusion directly.
