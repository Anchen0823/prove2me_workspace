## DAG wiring, 25 September 2026 — the goal now has two accepted decompositions

The goal `ZetaNine.irrational_zeta_nine` previously stood as a bare open leaf with **no** children in the platform dependency graph. It now carries two accepted proof-sketch decompositions, mirroring the two main lines of the local DAG.

| route | accepted children |
|---|---|
| one-form | `ZetaNine.irrational_of_small_nonzero_integer_forms` (**Proved**) + `ZetaNine.exponentially_small_nonzero_forms_of_zeta_nine` (**Open**) |
| two-form | `ZetaNine.irrational_of_two_small_integer_forms` (**Proved**) + `ZetaNine.exponentially_small_independent_forms_of_zeta_nine` (**Open**) |

Three new fully general lemmas are `Proved` and are the formalisable core of local nodes **TP** and **FQ**:

* `ZetaNine.irrational_of_small_nonzero_integer_forms` — a real number admitting nonzero integer forms of arbitrarily small absolute value is irrational. The criterion half of TP.
* `ZetaNine.taylor_sign_implies_kernel_sum_pos` — a strictly positive kernel with all samples at or beyond the expansion point, a polynomial whose Taylor coefficients there are all nonnegative, summability, and one positive sample force a strictly positive complete sum. The positive-kernel half of TP.
* `ZetaNine.quadrature_exact_of_moments` — agreement of a linear functional with a five-node rule on the moments of degrees zero through four forces agreement on every quartic. The exact algebraic core of FQ.

Five milestones now link them: `TP1`, `TP2`, `FQ1`, `R1`, `R2`. Every statement was read back blind by an independent auditor before publication.

**Honest scope of the two reductions.** Both open children are *strictly stronger* than the goal and are **not** equivalent to it: they demand approximations of a fixed exponential quality, which a general irrational number need not admit. The Lean content of the two reductions is a short final assembly, and the mathematical work lives entirely in the open child — neither child is claimed proved. Note also why the obvious shorter child was rejected: a child stated merely as "small integer forms exist" is *equivalent* to the goal once a criterion is available, so it would be a disguised restatement rather than a decomposition.

**Deliberately not wired.** There are still no Lean definitions of the concrete construction (coefficient matrix $F_n$, saturated kernel, Smith data, weighted areas, congruence-lattice minima). So the local reductions $V\leftarrow VA,Q,X$, $VA\leftarrow VB,Y$ / $VD,YD,H,Z,Y$, $VB\leftarrow VC,H,Z$, $T5\leftarrow FD,FC$ and $J\leftarrow V,S$ are **not** posted as platform decompositions, and the milestones for X, VB, VC, VD, S, J, T, TG, TS, T5, FD, FM and CP remain unlinked. A reduction whose parent has free parameters cannot import closed child theorems, so a genuine multi-level graph over the concrete nodes needs the definition layer first; the arrow arguments themselves are elementary once the objects exist. Building that layer — definitions plus one statement item per node — is the next step for this mission.

The goal remains **Open**.
