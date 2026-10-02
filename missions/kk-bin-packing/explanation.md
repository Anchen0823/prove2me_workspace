For an instance $I$ and a trace of Algorithm 2 with $k\geq 2$ and $g>0$, the bins present after Step 3 form a packing of the pieces whose sizes exceed $g$. Writing $t$ for the number of loop iterations and $X_i$ for the number of principal bins in iteration $i$, their number satisfies

$$
|P_{\mathrm{Step\,3}}|
\leq \sum_{i=0}^{t-1}X_i
+t\,2k\left(2+\log\frac1g\right)
+2+\frac{2}{1-1/k}\log\frac1g.
$$

The proof separates conservation of pieces, feasibility of each bin, and counting. This supplies the packing justification together with the estimate in Karmarkar and Karp, FOCS 1982, p. 317, first display in the left column.

Geometric grouping sorts the current instance in nonincreasing order and divides it into consecutive groups. In every group after the first, the retained prefix is represented by pairs of actual and rounded sizes, while the complementary suffix belongs to the separately packed instance. The first group also belongs to that instance. The take/drop identity and concatenation of the groups therefore give the exact multiset identity

$$
\operatorname{map}_{\mathrm{actual}}(\operatorname{geomPairs}(k,K))
+\operatorname{geomJ}'(k,K)=K.
$$

Every actual size in a retained prefix is at most the head of its group, which is its rounded size. The input-instance hypothesis makes the initial pieces positive, and conservation of pieces at each iteration preserves nonnegativity of the remaining instance. Its rounded sizes are therefore nonnegative as well. Each principal bin is matched with a feasible configuration whose sizes belong to the rounded instance, and its rounded pieces form a submultiset of that configuration. Nonnegativity then shows that its actual load is at most the load of the configuration, hence at most one. The other bins are legal by the trace's packing conditions.

At each iteration the principal bins use a submultiset of the retained pairs, and the next instance consists exactly of the unused actual pieces. Combining this fact with the grouping identity shows that the bins produced in that iteration and the next instance partition the current instance. Iterating this equality and finally adjoining the packing of the terminal instance proves that the Step 3 bins contain exactly the input pieces of size greater than $g$.

The matching with principal configurations also preserves the number of bins. Replicating each configuration according to the floor of its LP weight gives

$$
|B_i|=\sum_{c\in\operatorname{supp}(x_i)}\lfloor x_i(c)\rfloor_+=X_i.
$$

The trace bounds the number of separately packed bins in each iteration by the same quantity $2k(2+\log(1/g))$, and bounds the terminal packing by $2+2\log(1/g)/(1-1/k)$. Summing these bounds proves the displayed estimate. Empty bins are counted throughout, and the argument also covers the empty sum when $t=0$.

Source: [Karmarkar–Karp, An Efficient Approximation Scheme for the One-Dimensional Bin-Packing Problem](https://pagesperso.g-scop.grenoble-inp.fr/~newmana/OptApproxFall2016/Karmarker-Karp-BinPacking.pdf), pp. 315–317.
