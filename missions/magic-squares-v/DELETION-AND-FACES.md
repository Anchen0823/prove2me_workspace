# Deletion identities and orthant-section faces

The general matching-covered interval Euler identity remains open. This
increment proves two substantive parts of the intended route without assuming
that identity.

## Finite inclusion-exclusion

`SupportIntervalIE.lean` proves, for arbitrary finite sets D and B, that

    sum_{D subset C subset B} a(C)
      = sum_{S subset D} (-1)^|S| [B minus S has a perfect matching].

Its underlying finite-set theorem applies to any rational functions satisfying
f(A) = sum_{C subset A} g(C). There is no D subset B assumption.
`MatchingDeletion.lean` proves cancellation whenever D is nonempty and B minus D
contains a perfect matching: that matching survives every deletion S subset D,
and the alternating Boolean sum is zero. Thus an entire class of intervals is
now handled for arbitrary n. Intervals without such a complementary matching
still require an argument.

## Face structure

The three `Orthant*` modules work over any linearly ordered field. For a linear
subspace L of a finite coordinate space, let C be its intersection with the
nonnegative orthant. Every cone face of C is obtained by imposing additional
coordinate zeros, and every such constraint defines a face.

The proof constructs a point in each face whose support contains the supports
of all points in that face. A sufficiently small positive multiple of any
compatible nonnegative vector can be subtracted from this point while remaining
in C; the face axiom then puts that vector in the face.

This establishes the geometric support description, not the Euler relation.
Next, specialize the subspace to matrices with equal row and column sums and
connect nonzero supports to matching-covered boards. The pinned Mathlib already
contains `exists_eq_sum_perm_of_mem_doublyStochastic` in
`Analysis/Convex/Birkhoff.lean`; reuse its Birkhoff decomposition for this bridge.
The remaining major obligation is the interval Euler relation itself.

## Verification

The five new modules compiled successfully in the pinned Lean 4.33.1 environment
(8743 build jobs). The generic interval identity, its complementary-matching
corollary, and the face classification have only `propext`, `Classical.choice`,
and `Quot.sound` as axioms. See `verification/deletion-face-build.log` and
`verification/deletion-face-axioms.log`. Platform receipts are tracked separately
from local compilation; the mission root remains Open.
