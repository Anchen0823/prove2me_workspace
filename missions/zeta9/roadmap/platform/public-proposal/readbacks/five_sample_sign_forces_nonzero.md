# Blind read-back: Zeta9Note.five_sample_sign_forces_nonzero

**Verdict: FAITHFUL**

Independent audit of the draft statement only (no proofs, no mission description,
no author commentary supplied to the auditor).

## Checks
Name in file matches the filename: yes.
Elaborates against Mathlib revision 0df444a3 (Lean 4.33.1): yes (`lake env lean`, exit 0).

Duplicate or inconsistent hypothesis sets: none.

## Satisfiability
Satisfiable: the same quadrature witness, with p nonzero of degree ≤ 4; five distinct nodes forbid a nonzero polynomial from vanishing at all of them.

## Trivialization
No trivializing premise. Injectivity of the nodes and positivity of the weights are essential; dropping either makes the statement false.

## Flag
Cross-item note: this item is logically subordinate to `quadrature_exact_of_moments` (it combines it with a sign argument); they share the same moment setup. Not redundant, but a reviewer may note the dependence.
