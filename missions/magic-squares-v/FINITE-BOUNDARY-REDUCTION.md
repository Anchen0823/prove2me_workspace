# A finite combinatorial sufficient condition for the entire root

Date: 2026-09-22. This is a conditional proof architecture. The finite identity
below is **not proved in Lean** for arbitrary order. The public child is now
`MagicSquares.matching_boundary_euler` (`c44cf304-6efb-4853-bedd-7a2a604fb3f2`).
The standalone reciprocity reduction was uploaded as submission
`e7b0fc82-a39c-4c92-b7c8-b53c79c7e3a5` and received **SKETCH_ACCEPTED**; consult
`submissions/boundary-reciprocity-verdict.json` for its server verdict.

An audited mathematical derivation via Eulerian face lattices and dual Weisner
is given in [MATCHING-BOUNDARY-SOURCE.md](MATCHING-BOUNDARY-SOURCE.md).
`MatchingBoundaryEasyCase.lean` proves the branch `phi ⊆ D` with no remaining
hypothesis. The cancellation branch `phi ⊈ D` is the substantive open input.

## The remaining hypothesis

For a board C, put

$$a(C)=\sum_{S\subseteq C}(-1)^{|S|}
\mathbf1_{\{C\setminus S\text{ contains a perfect matching}\}}.$$

The previously proved `sB_eq_alternating_hasPerm` identifies this finite sum
with `sB n C`. A realizable support is precisely a nonempty matching-covered
board when n is positive, by `isSupport_iff_perm_coverage`.

Take realizable supports D contained in B, and the support phi of a perfect
matching contained in B. The new finite boundary hypothesis is

$$\sum_{\substack{B\setminus\phi\subseteq C\subseteq B\\D\subseteq C}} a(C)
=\begin{cases}a(B),&\phi\subseteq D,\\0,&\phi\not\subseteq D.\end{cases}$$

Every object here is finite. There is no counting-polynomial evaluation at a
negative argument in this expanded statement. `FiniteBoundaryEuler n` uses the
equivalent `sB` notation to reuse the existing formal interfaces. It is a
sufficient condition, not an asserted equivalence to the mission root.
`MatchingBoundaryCriterion n` expands both coefficients and realizable-support
guards into finite matching predicates. Its equivalence to `FiniteBoundaryEuler n`
for positive n is also formalized.

## Why this would finish the proof

Write F_B for the closed-support polynomial and E_B(X)=qB(B)(X-1) for the
exact-support polynomial. Summing the finite hypothesis over matrices at a
positive level, then subtracting the matching, gives

$$\sum_{B\setminus\phi\subseteq C\subseteq B} a(C)F_C(x)
=a(B)F_B(x-1).$$

Polynomial uniqueness extends the equality to rational x. This is
`finiteBoundaryEuler_implies_boundaryBalance`.

Strong induction on the board now proves

$$E_B(-x)=a(B)F_B(x).$$

For a non-realizable board, both E_B and a(B) vanish. On a realizable board,
the exact-support permutation recurrence expresses the first difference of
E_B(-x) using proper subboards. The inductive hypotheses and boundary balance
give the same first difference as a(B)F_B(x). Their values at zero also agree:
E_B(0)=a(B), and F_B(0)=1. Equal first differences and equal initial values
determine the polynomials. This is `normalized_reciprocity_of_boundaryBalance`.

For the full board U, the all-ones translation gives E_U(x+n)=P(x), while
F_U=P. Consequently

$$P(-n-x)=a(U)P(x).$$

The polynomial is nonzero since P(0)=1. Comparing leading coefficients yields
a(U)=(-1)^degree(P), and the already-proved degree `(n-1)^2` reduces this sign to
`(-1)^(n-1)`. Thus **no separate proof of the sign of a(U) is needed on this
route**. Existence and negative-root vanishing are already proved, so the
reciprocity result completes the root conditional on the single finite hypothesis.

## Formal files and limits

- `PolynomialDifference.lean`: first-difference uniqueness.
- `FiniteBoundaryBalance.lean`: finite condition to weighted counting balance.
- `ReciprocityPropagation.lean`: support induction and normalized reflection.
- `ReflectionSign.lean`: leading-coefficient determination of the scalar.
- `ReciprocityFromBoundary.lean`: the exact reciprocity and mission-root
  conclusions, with `FiniteBoundaryEuler n` as an explicit argument.
- `MatchingBoundaryCriterion.lean`: the completely finite formulation and its
  equivalence to the formal induction hypothesis.

All files are under `examples/magic-squares/spencer/`. They import no platform
theorem placeholders. Standard-axiom checks on conditional theorems do not
remove their explicit mathematical hypothesis.

The experiment `scripts/check_permutation_boundary_euler.py` found no failure:
orders 1, 2, and 3 were exhaustive (1, 8, and 1308 cases); order 4 used 600
recorded deterministic samples. These 1917 cases are evidence only, not a
general proof or a Lean certificate. The unresolved step is to prove the
displayed finite identity for all orders and boards; its universal difficulty
cannot be inferred from these small cases.

## Local verification

The complete chain builds successfully in pinned Lean 4.33.1 (8736 jobs).
Eleven declarations, including the conditional root theorem and the explicit
finite-criterion adapter, have only `propext`, `Classical.choice`, and
`Quot.sound` as axioms. There is no `sorryAx`. The still-unproved criterion is
an explicit theorem argument, not an extra axiom or a hidden placeholder.
Source hashes and logs are recorded in `verification/boundary-reduction-record.json`.
