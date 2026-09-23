# Next work after closed-support polynomiality

## Complete: no remaining Mission V proof work

`MissionVCompleted.lean` builds and proves the exact mission root with standard
axioms only. `MatchingIntervalEuler.lean` closes the finite boundary child
through the perspective-shadow route. Submission
`b6362b1e-e4ba-46ae-b278-8b4ca0bf615e` was **ACCEPTED**. Fresh platform queries
confirm child, reciprocity and root are **Proved**, and all **8/8** milestones
are completed. The mathematical tasks in the historical sections below have been
superseded by this complete proof; do not keep developing alternative Euler
theory to finish this mission.

## September 23: finite-dimensional slicing completed

`CompactConvexValuation.lean` now proves the compact-convex indicator relation
in every finite dimension, by slicing. Its integrated Lake build passed.
Do not repeat this dimension induction. Next prove relative-interior Euler
signs and the local face Euler relation; see [EULER-SLICING-PLAN.md](EULER-SLICING-PLAN.md).

## September 23: coefficient bridge completed

`MatchingMobius.lean` proves the coefficient is minus the bottom Mobius number
and transfers the entire interval sum. `SemiMagicFaceMobius.lean` transports the
identity to the geometric face poset. Both compile without extra axioms. See
[MOBIUS-BRIDGE.md](MOBIUS-BRIDGE.md). Focus on the geometric local Euler relation;
do not repeat coefficient identification or the face-support correspondence.

The coefficient formula is now platform **Proved** (submission
`a3ef28e8-7f34-45b9-bafe-469d3037038d`). The real-line Euler relation is locally
proved for closed intervals and for compact convex sets allowing empty sets.
Continue with compact convex slices in finite-dimensional real coordinate
spaces; see [EULER-SLICING-PLAN.md](EULER-SLICING-PLAN.md).

## September 22 correction: use the live frontier

The face-support correspondence, including normalization and realization of
every matching-covered board, is now fully proved in
`SemiMagicFaceSupport.lean`. See
[FACE-SUPPORT-CORRESPONDENCE.md](FACE-SUPPORT-CORRESPONDENCE.md).
Focus next on the Euler relation itself and coefficient identification; the
geometric dictionary is no longer a missing theorem on the conic route.
Schneider's author manuscript (source manifest `research/schneider-source.json`)
provides an explicit Euler-valuation construction and local interval identity.

Latest completed foundations: [DELETION-AND-FACES.md](DELETION-AND-FACES.md).
The Boolean interval/deletion transform, complementary-matching cancellation,
and the coordinate-face classification of orthant sections are now proved.
Next use Mathlib's existing Birkhoff decomposition to connect this face
classification to matching-covered boards. The general face-interval Euler
relation remains the major missing theorem; these new results do not discharge it.

Latest formal refinement: [INTERVAL-EULER.md](INTERVAL-EULER.md). The weighted
Weisner cancellation and matching-core transfer are implemented, so the next
substantive target is `MatchingIntervalEuler`: the coefficient sum on each
nondegenerate matching-covered interval is zero. This remains unproved.

The finite child is now published as `MagicSquares.matching_boundary_euler`,
ID `c44cf304-6efb-4853-bedd-7a2a604fb3f2`. Reuse it; do not publish another
equivalent finite-boundary child. See `submissions/boundary-problem-job.json`.

The mathematical route is now specified in
[MATCHING-BOUNDARY-SOURCE.md](MATCHING-BOUNDARY-SOURCE.md): realize matching-covered
boards as Birkhoff faces, identify the Boolean coefficient using face Euler
relations and the matching core of an arbitrary board, then apply dual Weisner
in the face-lattice interval `[D,B]`. These geometric/lattice facts remain to be
formalized. `MatchingBoundaryEasyCase.lean` already proves the entire branch
where the chosen permutation support is contained in D. Focus on cancellation
in the opposite branch; avoid further small-order enumeration.

The latest local route is [FINITE-BOUNDARY-REDUCTION.md](FINITE-BOUNDARY-REDUCTION.md):
prove the single finite permutation-boundary Euler identity. Conditional on it,
support induction now propagates reciprocity to all rational arguments and the
leading coefficient fixes the sign. Thus a separate propagation theorem and
separate full-board sign assumption are no longer missing on this route.
The finite identity itself is still unproved; the root remains Open.

The order-four milestone and all translation/reflection bridges are now proved
or have accepted tracked reductions. The sole Open root leaf is
`MagicSquares.ehrhart_macdonald_birkhoff_pos`
(`985f7b0a-962f-4039-804c-794f2ce86533`), not the older milestone itself.
Do not re-submit the existing positive-count bridge or repeat small-order work.

The new local support-constant identities and a precise finite Euler problem
are documented in [SUPPORT-EULER.md](SUPPORT-EULER.md). The alternating-sum
formula and conditional propagation are proved; the finite cancellation
identity remains formalization work. The older plan below records the
September 20 state and is superseded on these points.

Date: 2026-09-20. Read the current verification records before doing any new
submission: the existence, vanishing, and root-reduction uploads each have a
saved submission ID. Poll those IDs instead of submitting duplicates.

## Main target: reciprocity

The unresolved input to the root reduction is
`MagicSquares.semi_magic_reciprocity`, theorem
`32ea160a-bf6c-4a8f-90f7-31289a3d3ba3`:

$$
P(-n-t)=(-1)^{n-1}P(t)\qquad(t\in\mathbb Z),
$$

for the polynomial representing $H_n$ on the natural numbers. Exact degree,
agreement at zero, and all the prescribed negative roots are now proved locally;
consult `verification/continuation-record.json` for their separate server status.

The next useful combinatorial interface is translation by the all-ones matrix:
strictly positive semi-magic squares of line sum $t$ correspond to nonnegative
ones of line sum $t-n$ when $t\ge n$, and none exist for $1\le t<n$.
This is a counting bijection, not yet a reciprocity proof. The remaining hard
step must relate polynomial values at negative arguments to these interior
counts with sign $(-1)^{(n-1)^2}=(-1)^{n-1}$. Once this holds on infinitely many
integer arguments, polynomial uniqueness gives the full reflection identity.

Do not infer that exact degree plus the known roots forces reflection symmetry;
those data are insufficient in general. Nor should the earlier face-lattice
Euler/sign identities be restored as prerequisites for polynomiality: the
closed-support induction has already removed that requirement.

## Independent milestone: order four

`MagicSquares.semi_magic_count_four`
(`f85e8a07-5809-4c91-84a4-cea1cb2a7939`) remains an independent open milestone.
With general degree-nine polynomiality now available, a finite exact counting
certificate plus polynomial interpolation is a possible route. Numerical
tables alone remain insufficient; the finite counts must be justified in Lean.
This milestone is not an assumption of the current root reduction.

## Validation boundaries

The two new standalone proofs import only Mathlib and `Def_MagicSquares`;
their axiom checks exclude `sorryAx`. The root reduction deliberately imports
three theorem mirrors. Its local axiom list includes `sorryAx` because these
files are statements with placeholders. Server-side dependency tracking, not
that local reduction check, determines whether the complete root is proved.
