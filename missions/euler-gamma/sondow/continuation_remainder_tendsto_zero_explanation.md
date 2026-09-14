For fixed $n>0$,
$$R_{n,N}\longrightarrow0.$$
On the open unit square, $(xy)^N$ tends to zero and is between zero and one. The kernel is positive and admits the integrable majorant
$$K_n(x,y)<16^{-(n-1)}xy/4.$$
Apply dominated convergence to the inner integral, dominated by $K_n(x,\cdot)$. Its integral is itself measurable and integrable in $x$, and dominates every inner remainder integral. A second application of dominated convergence gives the result. The Lean proof verifies measurability, integrability, domination and the almost-everywhere endpoint exclusions explicitly. It uses no open platform theorem.
