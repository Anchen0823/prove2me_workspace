# Orphan re-attachment — 2026-09-19

Goal: give mission membership to every published magic-square node that was
sitting outside all mission DAGs, using the captain path documented in
`references/mission_captain.md` §Milestones:

> Linking a `theorem_id` … is captain attestation that the theorem is faithful to
> the milestone's statement — **it also grants that theorem membership in the
> mission** … Unlinking a theorem never revokes the mission membership it granted.

The user confirmed on 2026-09-18 that he is the captain of these missions, so the
writes went through the normal account token.

## Before / after

| | before | after |
|---|---|---|
| magic-square nodes on the platform | 47 (9 definitions + 38 theorems) | 47 |
| in some mission | 25 | **43** |
| orphans | 22 | **4** |

Membership sources that had to be unioned, since neither alone is complete:

1. the four proposals' `items` — `GET /mission-proposals/<id>` returns `items` in
   `item_order` (the `/items` sub-path does not answer a GET);
2. the live missions' milestone links — `GET /missions/<id>/milestones`.

## What was attached (18 milestones, all `201`)

Record with ids: `record.json`. Raw payload: `milestones.json`.

### Mission I `6d8463b5` — MacMahon's order-three enumeration (12 new milestones)

| theorem | id | milestone title |
|---|---|---|
| `magic_count_three_otherwise` | `fb4507f0` | MacMahon (1915) — the 3 ∤ t case of the order-three count |
| `magic_count_two` | `821e65d7` | BCCG (2003) §2 — order-two magic count |
| `pandiagonal_count_two` | `f7c75790` | BCCG (2003) §2 — order-two pandiagonal count |
| `pandiagonal_count_three` | `e6cecde0` | BCCG (2003) — order-three pandiagonal count P_3 |
| `panmagic_count_three` | `adc01be4` | order three — the two-direction panmagic count |
| `panmagic_is_magic` | `1ece0a73` | general n — every panmagic square is magic |
| `magic_constant_of_normal` | `2b184629` | normal squares, general n — the magic constant |
| `total_sum_eq_n_line_sum` | `426e247c` | semi-magic squares, general n — total sum = n · line sum |
| `transpose_preserves_magic` | `3b7c0d09` | symmetries, general n — transposition |
| `flipHorizontal_preserves_magic` | `0bd2ee84` | symmetries, general n — horizontal reflection |
| `flipVertical_preserves_magic` | `9b89d44c` | symmetries, general n — vertical reflection |
| `affine_preserves_magic` | `2e82f714` | symmetries, general n — affine substitution |
| `symmetric_magic_count_two` | `2f881f90` | BCCG (2003) §2 — order-two symmetric count |

(13 rows; `symmetric_magic_count_two` was posted separately, id
`aa767751-3ebf-42ed-b7c5-3ad51d025bee`.)

### Mission II `a030a222` — MacMahon's semi-magic enumeration (1)

| `semi_magic_count_two` | `86515ed9` | BCCG (2003) §2 — order-two semi-magic count |

### Mission III `c9b6fe9e` — the classification of order-three normal squares (4)

| `normal_order_two_none` | `f342d9be` | order two — there is no normal magic square |
| `normal_order_three_constant` | `08463353` | order three — the magic constant is 15 |
| `normal_order_three_center_five` | `337eccfa` | order three — the centre is 5 |
| `normal_order_three_associative` | `3a365b32` | order three — normal squares are associative with complement 10 |

Milestone counts afterwards: Mission I 18, Mission II 5, Mission III 5.

## What is still orphan, and why

**4 nodes, all of them definitions**, which have no `theorem_id` and therefore
cannot be attached by a milestone:

| definition | id |
|---|---|
| `MagicSquaresTransforms` | `667c7c46-2268-4c23-9bda-5a2fc62d941d` |
| `MagicSquaresNormal3` | `2581f8bc-149c-4259-b2c6-858f0d62a9b5` |
| `MagicSquaresPandiagonal` | `95bcf1fc-345e-4db9-ae0c-cc8d9dba9fb2` |
| `MagicSquaresMostPerfect` | `1d501cfa-7208-4653-b5fe-8ead53e0beb8` |

Verified state: 47 nodes, 43 with mission membership, 4 orphan.

The only remaining path to membership is a **proposal reference item** —
`{"kind": "reference", "theorem_id": …}`. The Mission V proposal (see
`../magic-squares-v/DESIGN.md`) should carry all four of them as reference items,
which closes this out.

## Tooling

* `tmp/orphans.py` — enumerates magic-square nodes by search.
* `tmp/probe_membership.py`, `tmp/membership2.py`, `tmp/proposal_items.py` —
  the negative results (which endpoints do *not* expose membership).
* `tmp/dag_members.py` — the working membership reader (proposal detail endpoint).
* `tmp/reattach.py` — the writer.
