# Euler relation via slices: implementation target

**Update:** the compact-convex indicator relation is now used by the proved
perspective-shadow cancellation, which closes Mission V locally without
general relative-interior signs or a general local face Euler theorem. See
`MissionVCompleted.lean` and `PERSPECTIVE-CANCELLATION-PLAN.md`. The further
general-Euler work discussed below is not required for this mission.

The coefficient-to-Mobius bridge is proved. The remaining geometry should be
attacked through a dimension induction, following the slicing idea in
Schneider's Theorem 2.3 (source manifest `research/schneider-source.json`).

The first step is now proved in `ClosedIntervalValuation.lean`: a rational linear
combination of indicators of nonempty closed real intervals that vanishes
pointwise has total coefficient zero. Degenerate intervals must be included.
For each right endpoint r, evaluate at r and just to its right, before any
other endpoint. The difference isolates the sum of weights ending at r.
Summing these groups gives the result.

`CompactRealValuation.lean` extends the relation to finite families of compact
convex subsets of the real line, including empty sets. A nonempty member is
identified with its closed interval between infimum and supremum; an empty
member has Euler weight zero. Both modules now compile successfully.

`ClosedIntervalEuler.lean` proves the indicator identity for an open interval
as its closed interval minus both endpoint singletons, and independence of
total coefficients for equal finite closed-interval/singleton representations.
Its targeted Lake build also passes.

This has now been extended to compact convex subsets of real finite coordinate
spaces in `CompactConvexValuation.lean`. The dimension induction slices by the
first coordinate. `CompactConvexSlices.lean` proves compactness using the tail
image of the closed hyperplane section, proves convexity, and identifies slice
nonemptiness with membership in the first-coordinate projection.
`CompactConvexProjection.lean` provides the compact convex projection and the
zero-dimensional base case. The integrated Lake build passed (8711 jobs).

The proved relation establishes the well-definedness needed for an additive
Euler functional on finite linear combinations of compact-convex indicators:
pointwise-zero combinations have total nonempty weight zero. An actual
linear-map packaging has not yet been implemented. The next mathematical work
is the relative-interior/sign argument and finite face decomposition needed
for the local Euler relation. The indicator relation alone does not finish
Mission V.
