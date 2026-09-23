# Direct interval cancellation through a perspective shadow

The compact-convex indicator relation now provides a proved route to the required
upper-interval cancellation without first developing dimension signs for every
relative interior. This route closes the local Mission V root; it does not
claim a general local Euler theorem.

Let P be a nonempty compact intersection of an affine subspace with the
coordinate nonnegative orthant. Let D be a finite nonempty collection of
coordinates. Suppose q belongs to the affine subspace, is positive on D,
nonpositive on its complement, and lies outside P. Choose a linear functional
l such that d(x) = l(x-q) is positive for every x in P. Consider

    f(x) = (x-q) / d(x).

For i in D let F_i = {x in P : x_i = 0}. The intended argument is:

1. f(P) and all f(F_S), where F_S is the intersection for i in S, are compact
   convex sets. Compactness follows from positive denominators and continuity;
   convexity follows from reweighting a convex combination by its denominators.
2. Each ray from q that meets P has a last point in P. That point has a zero
   coordinate in D: otherwise every zero coordinate has q_i <= 0, and a small
   extrapolation remains in the orthant and affine subspace, a contradiction.
   Thus f(P) is covered by the f(F_i).
3. A ray has at most one point in the union of the F_i. Indeed two such points
   x = q + t(y-q), t > 0, force t >= 1 from a zero coordinate of x and t <= 1
   from a zero coordinate of y. Therefore perspective images preserve all
   nonempty intersections of these coordinate faces.
4. Apply indicator inclusion-exclusion to the cover of f(P), then the proved
   compact-convex indicator relation. Since f preserves nonemptiness, this gives

       sum_{S subset D} (-1)^|S| [F_S nonempty] = 0.

For a matching-covered proper pair D < B, take P to be the doubly stochastic
polytope supported on B. Positive support realizations x_D and x_B give
q = (1+epsilon) x_D - epsilon x_B. A sufficiently small positive epsilon makes
q positive on D and negative on B minus D, and keeps the affine row/column
constraints. The sum of coordinates outside D supplies l with d > 0 on P.
Nonemptiness of F_S is precisely existence of a perfect matching in B minus S.
The already proved interval inclusion-exclusion formula would then finish
MatchingIntervalEuler, hence the existing boundary and reciprocity reductions.

## Formal status

- `CompactConvexRepresentation.lean`: equality of finite indicator
  representations preserves the total nonempty weight (compiled).
- `PerspectiveBoundary.lean`: uniqueness of a boundary point on a ray and
  injectivity of normalized rays on this boundary (compiled).
- The small extrapolation lemma and compact last-point argument are proved.
- Perspective convexity, compact last-point existence, cover, finite
  inclusion-exclusion integration, and the matching-polytope specialization
  are now all proved and connected through `PerspectiveCancellation.lean`,
  `SupportExtensionCancellation.lean`, `SupportedStochasticPolytope.lean`,
  `SupportedStochasticExistence.lean` and `MatchingIntervalEuler.lean`.
  `MissionVCompleted.lean` derives the entire mission root without additional
  assumptions; its integrated build and axiom audit passed.

The source paper's equations (19)-(22) use relative-interior signs and angle
cones. The direct shadow argument above is an alternative proposed here;
it is not being attributed verbatim to Schneider's theorem.
