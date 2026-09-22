# Prove2Me boundary-route refresh

Refreshed at `2026-09-22T21:51:05+08:00` with authenticated, read-only
`python -X utf8 scripts/p2m_api.py get` calls against `https://prove2.me/api/v1`.

## Current targets

| Target | ID | Current platform status |
| --- | --- | --- |
| Full BCCG Theorem 1 root | `a8fa7ac8-321b-492a-9e96-d5303081a54f` | Open |
| Semi-magic reciprocity | `32ea160a-bf6c-4a8f-90f7-31289a3d3ba3` | Open |

## Current root decomposition and submissions

The root has one accepted sketch submission,
`b67b135f-bf4e-46d1-b4a9-14dd91d176dd`.  Its active decomposition has three
theorem children: polynomial existence is Proved, vanishing is Proved, and the
reciprocity target above remains Open.  Consequently the root remains Open.

## Current reciprocity decomposition and submissions

The reciprocity target has two accepted sketches, both from `Tamas Fulop`:

* `f7915b26-99d3-4f98-a646-72fb46d144c4`, whose active children include the
  deprecated-and-Disproved `MagicSquares.interior_reciprocity` and the Proved
  positive-shift child;
* `b8a5089c-c1a2-477c-a3f3-39519d516f6d`, whose active open child is
  `MagicSquares.interior_reciprocity_pos`
  (`5ca89b06-1944-4bca-8ae9-160021073541`) and whose positive-shift child is
  Proved.

Neither target's current submissions or decompositions names a finite matching
boundary Euler theorem, `FiniteBoundaryEuler`, `BoundaryBalance`, or the
Boolean-Mobius/permutation-boundary route.  A broad `/theorems` query with a
`search=FiniteBoundaryEuler` parameter was not usable as a duplicate search: it
returned the full global listing (90,912 results), rather than a filtered set.
The targeted target/decomposition/submission inspection and local source search
therefore found no duplicate child in this route, but do not establish a
platform-wide global nonexistence claim.

## Submission readiness boundary

The local verified route gives a new conditional reduction:

`FiniteBoundaryEuler -> BoundaryBalance -> normalized reciprocity -> full
reciprocity -> root`.

It is suitable for a new platform **conditional sketch/decomposition path** if
the platform accepts a new finite combinatorial child.  It is not yet a proof
submission of either existing Open target: `FiniteBoundaryEuler` remains an
explicit unproved sufficient condition.  No platform write was made during this
refresh.
