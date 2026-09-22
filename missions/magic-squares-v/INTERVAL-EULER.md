# The remaining matching-support interval identity

The next mathematical target is now a finite interval sum. For the public
coefficient `a(C) = matchingEulerCoefficient n C`, prove

$$\sum_{D\subseteq C\subseteq B} a(C)=0$$

whenever `n >= 1`, both D and B are nonempty matching-covered boards, and
`D` is a proper subset of `B`. This is `MatchingIntervalEuler n` in
`MatchingIntervalReduction.lean`. It is still an unproved hypothesis.

The implication from this identity to the public boundary criterion is now
implemented. It uses the following components:

1. `MatchingCore.lean` defines the union of all allowed permutation supports.
   It proves monotonicity, idempotence, matching coverage when a matching exists,
   preservation of contained matching-covered boards, and transfer of interval
   weight sums to the matching core when the weight vanishes on other boards.
2. `MatchingCoefficientSupport.lean` proves that the public coefficient equals
   the previously constructed support-polynomial constant and vanishes on
   non-matching-covered boards.
3. `WeightedWeisner.lean` proves a general finite-lattice cancellation theorem:
   if every weighted prefix sum from d to x is zero for a <= x <= b, then the
   fibre with c join a = b also has zero total weight. Its proof only uses
   regrouping finite sums and finite-order induction, not topology or a
   pre-existing Mobius function.
4. `MatchingIntervalReduction.lean` takes a = D union phi. In the difficult
   branch phi is not contained in D. Every relevant matching core then properly
   contains D, so the hypothesized interval Euler identity applies. The easy
   branch has a singleton summation set, already handled separately.

This yields the checked implication

`MatchingIntervalEuler -> MatchingBoundaryCriterion -> reciprocity -> mission root`.

The first predicate is a sufficient condition; an equivalence has not been
claimed or proved. Nothing here proves the interval Euler identity itself.
The classical geometric justification still requires the Birkhoff-face
description and Euler relations, as explained in `MATCHING-BOUNDARY-SOURCE.md`.
The new finite-algebra implementation avoids needing a formal Mobius-function
theory or a separate dimension-sign computation in the downstream reduction.

The public boundary child remains the existing
`MagicSquares.matching_boundary_euler` (`c44cf304-6efb-4853-bedd-7a2a604fb3f2`).
Do not create another Open platform child merely to rename this remaining gap.
