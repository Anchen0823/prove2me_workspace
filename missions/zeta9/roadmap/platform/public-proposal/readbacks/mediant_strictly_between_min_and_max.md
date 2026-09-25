# Blind read-back: Zeta9Note.mediant_strictly_between_min_and_max

**Verdict: FAITHFUL**

Independent audit of the draft statement only (no proofs, no mission description,
no author commentary supplied to the auditor).

## Checks
Name in file matches the filename: yes.
Elaborates against Mathlib revision 0df444a3 (Lean 4.33.1): yes (`lake env lean`, exit 0).

Duplicate or inconsistent hypothesis sets: none.

## Satisfiability
Satisfiable: a = (0,1,0,0,0), b constant 1, uniform weights; the ratio of weighted sums is 1/5, strictly between 0 and 1. Positive denominators keep the denominator sum nonzero.

## Trivialization
No trivializing premise; hb (positive denominators) is essential and is assumed.
