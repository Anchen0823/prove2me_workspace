# Magic Squares V reciprocity audit — 2026-09-22

## Live frontier

Mission `e06131f8-1bf5-47c4-b8f4-507f107269e0` has one Open milestone:
`MagicSquares.semi_magic_reciprocity` (`32ea160a-bf6c-4a8f-90f7-31289a3d3ba3`),
at live milestone `e980f5b0-9805-429d-bad3-01d05405b88d`.

The other seven milestones are completed, including the all-natural polynomial,
vanishing, and order-four count. The correct milestone id uses `429d`; its
history is empty. The mission has one comment, the older order-four volume
correction; no discussion entry concerns reciprocity.

The root `a8fa7ac8-321b-492a-9e96-d5303081a54f` now has precisely one Open
leaf:

```
985f7b0a-962f-4039-804c-794f2ce86533
MagicSquares.ehrhart_macdonald_birkhoff_pos
```

This is the positive-dilation Birkhoff-polytope reciprocity statement. Its
formal statement is saved in `root-open-leaf-theorem.json`; it uses an explicit
`Set.ncard` of positive integral points in a rational dilation. It has no
submissions and no non-definition decomposition.

## Existing reductions

`semi_magic_reciprocity` is Open and has two `SKETCH_ACCEPTED` reductions:

- `f7915b26-99d3-4f98-a646-72fb46d144c4` uses a Disproved and deprecated child.
- `b8a5089c-c1a2-477c-a3f3-39519d516f6d` is the corrected route; source is
  `reciprocity-sketch-b8a5089c-source.txt`. It imports Open
  `interior_reciprocity_pos` plus Proved `positive_shift_count`.

`interior_reciprocity_pos` is
`5ca89b06-1944-4bca-8ae9-160021073541`, Open, with one accepted sketch
`efca7551-ad8b-4f85-b976-415cea725b2f` (source saved locally). That sketch
already uses Proved small-positive interior emptiness, vanishing, and the
all-ones shift. Its remaining Open child is
`7a04de6e-94da-4423-add4-d1a79f131d05`,
`MagicSquares.interior_functional_eq_nat`.

The current root-leaf dependency graph has 43 nodes and 103 edges. A Kahn
topological pass removed all 43 nodes: no directed cycle was detected, and the
API reports no hidden deprecated sketches. The leaf itself has no submissions,
including none from the current account (`418b0711-62a5-416a-ba5d-876ae8758fe3`).
There is no reason to submit another copy of either existing bridge.

## Small-order assets

Existing Proved platform count nodes support independent small-order work:

- `611ea9c5-4346-49e1-800c-aa23be9f7303` — order one.
- `86515ed9-6bd4-4484-a3d2-a1be23ce7ac9` — order two.
- `55e2191d-be25-4e6d-af7a-4635a34e5c63` — order three.

The repository sources are `Solutions/Sol_MagicSquares_semi_magic_count_one.lean`,
`Solutions/Sol_MagicSquares_semi_magic_count_two.lean`, and
`Solutions/Sol_MagicSquares_semi_magic_count_three.lean`; the order-three
formula is also recorded in `examples/magic-squares/statements.lean`. The live
dependency graph already contains Proved specialized natural-functional
equations for orders one, two, three, and four, so these cases are not the
general-order blocker.

## Published-reference paths inspected

No locally stored original paper provides a concrete elementary proof of the
outstanding reciprocity statement. Relevant local paths only:

- `referpaper/README.md`
- `referpaper/Beck-Cohen-Cuomo-Gribelyuk - The number of magic squares, cubes and hypercubes (2003).pdf`
- `missions/magic-squares-v/SPENCER-ROUTE.md`
- `missions/magic-squares-v/S5-NOTES.md`
- `missions/magic-squares-v/CLOSED-SUPPORT.md`
- `missions/magic-squares-v/NEXT-STEPS.md`

No proof files, Lake configuration, or API state were modified.
