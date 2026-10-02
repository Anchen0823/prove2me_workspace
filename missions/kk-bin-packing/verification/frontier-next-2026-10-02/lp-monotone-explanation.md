If $A$ is a submultiset of an instance $B$ whose item sizes lie in $(0,1)$, then

$$LIN(A)\le LIN(B).$$

The proof transforms each feasible configuration solution for $B$ into one for $A$ with the same total weight. Configuration coverage is an inequality, so extra copies of retained item types cause no problem.

First suppose $A$ is nonempty and choose one item $a\in A$. From every configuration $c$ of $B$, delete all item types absent from $A$. If the resulting configuration is empty, replace it by the singleton containing $a$. Denote this transformation by $f$. Every resulting configuration is nonempty, uses only types present in $A$, and has size at most one: filtering can only decrease size because all items in $B$ are positive, and the replacement singleton has size less than one.

Push the nonnegative configuration weights forward along $f$, adding weights whenever several original configurations have the same image. Finite summation gives

$$lpCost(f_*x)=lpCost(x).$$

For a type $s$ present in $A$, a nonempty filtered configuration retains its original number of copies of $s$. If filtering empties a configuration, that configuration originally contained no copies of $s$, and replacement cannot reduce its coverage. Hence

$$\operatorname{count}_A(s)\le\operatorname{count}_B(s)\le\sum_c x_c\operatorname{count}_c(s)\le\sum_d(f_*x)_d\operatorname{count}_d(s).$$

Thus the pushed weights are feasible for $A$. All feasible costs are nonnegative. The feasible-cost set for $B$ is nonempty, since putting each item in its own singleton bin yields a feasible configuration solution. Therefore $LIN(A)$ is at most every feasible cost of $B$, and taking their infimum proves the assertion.

When $A$ is empty, the zero weighting is feasible and has cost zero. Nonnegativity gives $LIN(A)=0\le LIN(B)$, completing the proof.
