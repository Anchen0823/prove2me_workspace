# Face-support correspondence for the real semi-magic cone

The geometric dictionary is now explicit. Let L be the real linear subspace of
matrices whose row and column sums all agree, and let C be its nonnegative part.
For n >= 1 the faces of C, ordered by inclusion, are order-isomorphic to the
matching-covered boards together with the empty board, also ordered by inclusion.
The map sends a face to the coordinates used by any of its points.

`OrthantFaceOrder.lean` first proves this for a general orthant section and its
realized coordinate supports. A maximal-support point realizes each face's entire
support; support containment is equivalent to face containment. This yields both
an order isomorphism and finiteness of the set of faces.

`SemiMagicCone.lean` shows that a nonzero nonnegative matrix in L has strictly
positive common line sum. Dividing by that sum gives a doubly stochastic matrix
without changing positive support. `DoublyStochasticSupport.lean` identifies such
supports in both directions: Birkhoff decomposition supplies a matching through
each positive entry; averaging every allowed permutation realizes any
matching-covered board. `SemiMagicFaceSupport.lean` combines the results into
`semiMagicFaceSupportOrderIso`.

The zero vector is handled separately, so the empty board is present as bottom.
The theorem assumes n >= 1; no conclusion about the exceptional zero-order
conventions has been smuggled into the correspondence.

## Exact remaining mathematical work

An order isomorphism alone does not establish Eulerianity. The general interval
coefficient cancellation in `MatchingIntervalEuler` is still unproved. The next
proof must establish the relevant Euler relation, identify the coefficient with
the face weight, and transfer the resulting sum through this correspondence.
No additional conditional platform child is introduced merely to rename this gap.

Rolf Schneider's *Combinatorial identities for polyhedral cones*, Theorem 2.3,
constructs an Euler valuation by dimension induction. Equations (19)-(22) then
give global and local face Euler relations and the associated Mobius formula.
The local relation is the needed geometric input. This is a source roadmap,
not an available Lean theorem. The downloaded author manuscript is recorded
with a hash in `research/schneider-source.json`:
https://home.mathematik.uni-freiburg.de/rschnei/Comb.Ident.rev.pdf.
