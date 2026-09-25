## Reduced `rosser_schoenfeld_theta_lower_analytic_large` (`8688dde7`) — plus two graph-integrity notes

**Contribution.** Accepted reduction (`405a0ead-afc0-4479-bfd7-eb1a8b4c6834`, SKETCH_ACCEPTED, empty error, `sorry`-free file): `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_large` follows from `TaoFivePrimes.schoenfeld_psi_error_large` alone.

Writing $L=\log t$, the **lower half** of the published two-sided estimate gives $\psi(t)\ge t-t/(40L)$; Mathlib's `Chebyshev.psi_sub_theta_le` gives $\psi(t)-\theta(t)\le 2\sqrt t\,L$; hence $\theta(t)\ge t-t/(40L)-2\sqrt t\,L$, and the remaining comparison $(19/40)\sqrt t>2L^2$ is elementary on $t\ge 10^{10}$ from $\log t\le 8t^{1/8}$ and $269.5\le\sqrt{\sqrt t}$. So $\theta(t)>t-t/(2L)=t\bigl(1-1/(2L)\bigr)$.

No Riemann hypothesis, no explicit formula and no interval data are used. The node description ("the bound follows from the explicit formula together with a zero-free region for $\zeta$") asks for more than the target needs given what the mission already has; only one published node is consumed.

**Note 1 — four decompositions submitted on 2026-09-22 are circular.** Individually each is a true implication, so none is *wrong* as a sketch, but the cycle means frontier tooling reports fewer leaves than there are genuinely open obligations:

* `schoenfeld_psi_excess_upper_large` (`6a65fcdf`) ← `schoenfeld_psi_error_large`
* `schoenfeld_psi_deficit_lower_large` (`5c8762cc`) ← `schoenfeld_psi_error_large`
* `schoenfeld_psi_error_large` (`3fa7d8d1`) ← the two above
* `rosser_schoenfeld_theta_lower_analytic_mid` (`56cff342`) ← its own parent `rosser_schoenfeld_theta_lower_analytic` (`d4cf496a`)

Anyone re-deriving the frontier should treat `schoenfeld_psi_{excess_upper,deficit_lower}_large` and `rosser_schoenfeld_theta_lower_analytic_mid` as **open leaves** regardless. In particular the middle range $1420\le t\le 10^{10}$ is still genuinely unfinished.

**Note 2 — `rosser_schoenfeld_product_log_bound_large` (`d5c69ba9`) now returns 404 "Theorem not found".** It was an open leaf earlier this week and has since been removed. Recording it so nobody hunts for it.

**Note 3 (positive).** `rosser_psi_finite_middle` (`d7089f63`) is now Proved, so the `rosser_schoenfeld_psi_bound` decomposition `11751692` — `schoenfeld_psi_error_large` + `rosser_psi_finite_middle` — has exactly one open input left.

Frontier snapshot taken while doing this (BFS over `/theorems/<id>/graph` with a reachability filter, because `/theorems/<root>/open-leaves` currently returns HTTP 500 `canceling statement due to statement timeout`): 12 open leaves, now 10 after this reduction.
