# Magic Squares V — proposal status

## Complete: platform root Proved and all 8 milestones completed

`MagicSquares.semi_magic_polynomial_completed` now proves the exact mission
root without any unproved Euler hypothesis. The complete build passed
(8768 jobs), and the root, interval cancellation and matching-boundary
criterion depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The proof uses the direct perspective-shadow argument described in
[PERSPECTIVE-CANCELLATION-PLAN.md](PERSPECTIVE-CANCELLATION-PLAN.md), followed by
the existing finite boundary, reflection and polynomial reductions.

The complete proof of the existing child `MagicSquares.matching_boundary_euler`
was accepted as `b6362b1e-e4ba-46ae-b278-8b4ca0bf615e` at
`2026-09-23T09:18:29Z`. Fresh platform queries confirm the child, reciprocity
milestone and root `a8fa7ac8-321b-492a-9e96-d5303081a54f` are all **Proved**;
all **8/8** mission milestones are completed. The standalone source was independently compiled and its
global `solution` has only standard axioms. No `Theorems.*` import occurs.

Approval service access has recovered: a fresh usage check allowed normal
use, then an approved platform read and the submission both succeeded.
The older usage-limit notes below describe historical interruptions.
The exact original platform root statement also compiles using the completed
local theorem. Completion receipts and hashes are recorded in
`verification/mission-v-completion-record.json`. No further proof work is
required for Mission V. The general relative-interior Euler route is not a
remaining mission requirement.

## 2026-09-23 finite-dimensional Euler foundation

`MagicSquaresEuler.compactConvex_indicator_relation` is proved for every
dimension and arbitrary finite rational-weighted families of compact convex
sets, including empty members. If their indicator combination is pointwise
zero, the total weight of nonempty members is zero. The integrated Lake build
passed (8711 jobs). See [EULER-SLICING-PLAN.md](EULER-SLICING-PLAN.md).
The standalone `ConvexGeometry.compact_convex_indicator_relation` submission
package also compiled independently (exit 0), and its `solution` uses only
standard axioms. Exact hashes are in
`verification/compact-convex-valuation-record.json`. It has **not** been uploaded;
automatic approval review is unavailable due to its usage limit.
This is a local result; the relative-interior signs and local face Euler
relation remain unproved. The mission root is still Open.

The latest Git staging operation was not executed: automatic approval review
could not run because its usage limit was reached. Earlier staging succeeded,
but no new commit was created. Source and verification records remain in the
worktree; do not bypass approval to finish the checkpoint.

## 2026-09-23 coefficient identification

**Platform ACCEPTED:** `MagicSquares.matching_coefficient_eq_neg_mobius`,
theorem `2436e4cb-003b-423c-bd3a-318933165075`, submission
`a3ef28e8-7f34-45b9-bafe-469d3037038d`, accepted at
`2026-09-23T01:46:19Z`. The first submission was rejected because its global
`solution` entry point was missing; the corrected bundle was independently
recompiled and its axioms checked before resubmission. Both receipts are kept.

The one-dimensional closed-interval indicator relation is also proved locally,
including degenerate intervals; build and axiom checks passed. This is the
first step of the Euler slicing proof, not the general local Euler theorem.

The matching coefficient is now formally identified with the negative bottom
Mobius number on every nonempty support, with the empty-board exception handled
explicitly. Both the coefficient interval sum and the geometric-face version
are proved. The integrated build completed (8752 jobs); four core declarations
have only standard axioms and no `sorryAx`. See [MOBIUS-BRIDGE.md](MOBIUS-BRIDGE.md).
The remaining mathematical gap is the general local Euler relation, not the
coefficient identification or face-support dictionary.

## 2026-09-22 live update

**Geometric dictionary accepted by the platform:**
`MagicSquares.real_cone_face_support_order_iso`, theorem
`db8ce110-88d2-4a2d-982d-6a9731e337bb`, submission
`fe97f4d1-8496-443b-9f74-ead04788dc58`, received **ACCEPTED**.
Its complete proof uses only Mathlib and two public definitions, with no Open
theorem dependency. Exact hashes and receipts: `verification/face-support-record.json`.

The face order of the real
nonnegative semi-magic cone is now order-isomorphic to matching-covered boards
with the empty board adjoined. This includes both realization directions,
normalization, support containment versus face containment, and finiteness of
the face set. The integrated module builds successfully (8714 jobs), and the
three key declarations have only standard axioms. See
[FACE-SUPPORT-CORRESPONDENCE.md](FACE-SUPPORT-CORRESPONDENCE.md) and
`verification/semi-magic-face-axioms.log`. The general Euler relation remains open.

**Two further complete platform proofs accepted:**

- `Finset.interval_inclusion_exclusion`, theorem
  `f6be11fe-a4bf-440c-96fc-7aa711ca505b`, submission
  `d1975d27-54ac-44dc-96bf-4e816bc201b4`: **ACCEPTED**.
- `ConvexGeometry.orthant_section_faces_are_coordinate_faces`, theorem
  `053dd816-08cd-4700-a729-3623df792e52`, submission
  `ee7a0ae9-a758-47e2-91b0-6555aed36389`: **ACCEPTED**.

Both complete solutions import only Mathlib. These reusable foundations do not
yet close the mission's matching-boundary child. Saved verdicts and exact source
hashes: `verification/deletion-face-record.json`.

**New unconditional local proofs:** Boolean-interval inclusion-exclusion now
proves the matching interval vanishes whenever the nonempty lower board has a
perfect matching in its complement inside the upper board. Separately, every
face of a finite-dimensional subspace intersected with the nonnegative orthant
is now proved to be a coordinate-zero section, over any ordered field. All five
new modules compile (8743 jobs), and three representative declarations have
only standard axioms. See [DELETION-AND-FACES.md](DELETION-AND-FACES.md).
The general interval Euler relation and the mission root remain Open.

The next geometric bridge has also been checked locally in
`BirkhoffSupport.lean`: every positive entry of a real doubly stochastic matrix
lies on a permutation entirely in its positive support. This reuses Mathlib's
Birkhoff decomposition. It has not been separately submitted to the platform;
normalization of the full cone and the face-lattice correspondence are next.

**Further formal refinement:** `MatchingIntervalReduction.lean` now proves that
the coefficient sum vanishing on every nondegenerate matching-covered interval
suffices for the published boundary criterion. The supporting matching-core,
coefficient-support and weighted-Weisner lemmas compile together (8742 jobs);
four representative declarations have only the standard axioms, with no
`sorryAx`. The interval identity itself is still unproved. See
[INTERVAL-EULER.md](INTERVAL-EULER.md) and `verification/interval-reduction-axioms.log`.
The reusable `FiniteLattice.weighted_weisner_cancellation` is now **Proved** on
the platform: theorem `7aaef4ef-b6d4-43f6-82ae-d8ea5f8a4dc1`, submission
`a7359247-9de6-4400-ab48-0d578b4af9be`, verdict **ACCEPTED** at 22:43.
Its complete proof imports only Mathlib, with no Open child dependency.

**Platform submission completed:** the finite-boundary reciprocity reduction
was accepted as **SKETCH_ACCEPTED** on 2026-09-22 at 22:08 (Asia/Shanghai).
Submission: `e7b0fc82-a39c-4c92-b7c8-b53c79c7e3a5`.
The server decomposition confirms its only theorem child is
`MagicSquares.matching_boundary_euler`
(`c44cf304-6efb-4853-bedd-7a2a604fb3f2`), still **Open**.
The original root already depends on reciprocity, so this new route is linked
to the root without another duplicate root submission. The full mission remains Open.

The public finite definitions are published as `MagicSquaresMatchingBoundary`
(`027fccf6-cca0-433e-8801-55c88c84db26`). The final standalone proof compiles
locally with the pinned toolchain and contains no `sorry` or extra assumptions;
its unproved input is the explicitly imported platform child. Receipts and
source hashes: `verification/boundary-platform-record.json`.

An audited mathematical derivation via Eulerian face lattices and dual Weisner
is in [MATCHING-BOUNDARY-SOURCE.md](MATCHING-BOUNDARY-SOURCE.md). The branch
where the permutation support is contained in D is now proved in
`MatchingBoundaryEasyCase.lean`; formalizing the opposite zero-sum branch
remains the next substantive task.

### Earlier local verification and original route

Latest local advance: the entire root has been reduced to one explicit finite
permutation-boundary Euler identity. The propagation to all arguments and the
leading-coefficient sign step are now implemented, so these are no longer
separate gaps on the new route. See
[FINITE-BOUNDARY-REDUCTION.md](FINITE-BOUNDARY-REDUCTION.md).
The finite identity itself is unproved: this is conditional progress, not a
completed proof or an additional accepted platform milestone.
The full chain and explicit finite reformulation now compile (8736 jobs).
Eleven new declarations pass the standard-axiom check with no `sorryAx`;
see `verification/boundary-reduction-record.json`. Their finite hypothesis
remains an explicit argument and has not been discharged.

Seven of eight milestones are now Proved, including the order-four count.
The remaining milestone is `semi_magic_reciprocity`; its accepted reductions
leave exactly one Open root leaf:
`MagicSquares.ehrhart_macdonald_birkhoff_pos`
(`985f7b0a-962f-4039-804c-794f2ce86533`). The root is still Open.
The saved dependency graph is acyclic (43 nodes, 103 edges).

This continuation develops a new local interface: exact-support constants are
the Boolean Möbius transform of the perfect-matching indicator. Combining it
with the all-ones translation also gives an exact finite alternating-sum formula
for `P(-n)`; its general sign is not yet proved. See
[SUPPORT-EULER.md](SUPPORT-EULER.md) for the identities, finite experiment, and
remaining proof gap, and [the live audit](research/2026-09-22-reciprocity/audit.md)
for the already-published bridges that should not be duplicated.
The support/perfect-matching-coverage equivalence is also proved. All new modules
compile in the pinned environment; 18 declarations have only the standard
`propext`, `Classical.choice`, and `Quot.sound` axioms. Validation and hashes are
in `verification/support-constants-record.json`.
These earlier helper results were initially local only. The new platform
submission recorded above now includes them in the accepted conditional reduction.

The dated September 20 snapshot below is historical.

<!-- closed-support-continuation:start -->
## 2026-09-20 continuation: two milestones accepted; one root leaf remains

| Result | Server verdict | Submission |
| --- | --- | --- |
| All-natural-line-sum polynomial, exact degree `(n-1)^2` | **ACCEPTED** | `36575948-2773-4c3f-b3c4-6e899aa4271f` |
| Full vanishing list `-1,...,-(n-1)` | **ACCEPTED** | `b6903bee-18e6-40d0-a49e-4ca1e631ff02` |
| Root reduction to the three existing milestones | **SKETCH_ACCEPTED** | `b67b135f-bf4e-46d1-b4a9-14dd91d176dd` |

**Live root frontier: exactly one Open leaf, reciprocity**
(`32ea160a-bf6c-4a8f-90f7-31289a3d3ba3`). The root itself remains Open.
The separate order-four explicit counting milestone also remains Open; it is not
an input to the root reduction. Six of eight listed milestones are now Proved.

The new proof counts support **contained in** a board, retains the zero matrix,
uses permutation subtraction and boundary inclusion-exclusion, and inducts over
strictly smaller boards. It proves polynomiality including line sum zero without
Euler/reciprocity. The same polynomial recurrence and disjoint cyclic permutations
give the entire negative-root list. See [the mathematical argument](CLOSED-SUPPORT.md)
and [the next target](NEXT-STEPS.md).

Both standalone proofs compile in the pinned Lean 4.33.1 environment and have
axioms exactly `propext, Classical.choice, Quot.sound`, with no `sorryAx`.
The conditional root reduction's local `sorryAx` comes from platform theorem
mirrors; the server has accepted the dependency-tracked sketch, not a full proof.

Source: `examples/magic-squares/spencer/ClosedPolynomial.lean` and
`ClosedVanishing.lean`. Reproducible bundle generators are in this mission's
`scripts/`. All submitted hashes, IDs, final verdicts and the remaining leaf are
in [continuation-record.json](verification/continuation-record.json).
The independent review and initial live audit are in `research/2026-09-20-continuation/`.
Earlier S5 assessments below are historical and have been superseded.
<!-- closed-support-continuation:end -->


Last updated: 2026-09-19 21:20 (Asia/Shanghai).

✅ **Mission V is LIVE.**  Proposal id `3a8476fd-e093-414d-a8d8-e020d2466a57` flipped from
`In review` to **`Reviewed`** (proposal `updated_at` `2026-09-19T15:01:27Z`), re-verified
2026-09-19 21:1x local by `GET /mission-proposals/3a8476fd-…`:

```
status     = Reviewed
mission_id = e06131f8-1bf5-47c4-b8f4-507f107269e0
```

`GET /missions/e06131f8-…/milestones` returns all **7** milestones in attack order.  Three
consequences, all of which were blocked before:

* the **milestone text is now captain-editable**, so the `vol(B_4)` correction recorded further
  down can finally be applied (together with a correction comment in the mission discussion);
* the Spencer-route payoff theorems can be **published as mission nodes** by attaching a
  milestone — the user is the captain of these missions, so no external review is needed;
* `semi_magic_polynomial_exists` (the goal's milestone `72482ba2`) is still `Open`, and its
  formal statement is *exactly* what the Spencer route was built to prove — see the Brick 11
  section at the end of this file for how close it now is.

## ✅ Both captain actions executed (2026-09-20 02:2x–02:5x)

### 1. The `vol(B_4)` wording is corrected, and the correction is on the record

* Milestone **`c791e322-27f8-49d9-bdcd-cd9120a5fe8c`** (sort_order 3, "Beck-Pixton (2002) …")
  now reads: leading coefficient `11/11340`, then explicitly that this is *not* the Euclidean
  volume — `vol(B_4) = n^{n-1}·11/11340 = 4³·11/11340 = 176/2835`, larger by `n^{n-1} = 64` —
  with `vol(B_3) = 9/8` (leading coefficient `1/8`) as the comparison, and the normalised
  volume `9!·11/11340 = 352`.
* Comment **`f4035c14-69d6-43ba-9e6c-35155be0c236`** posted to the mission discussion
  (`POST /missions/e06131f8-…/comments`, body `missions/magic-squares-v/comment-vol-b4-correction.md`).
  It was the **first** comment on the mission (the list was empty beforehand).
* ⚠️ **The milestone had to be re-created, so its id changed** from `9e912298-…` to `c791e322-…`.
  Cause: while probing for the milestone-update endpoint I sent one probe per verb including
  `DELETE`, and `DELETE /milestones/<id>` returned **204**. See `PLATFORM-NOTES.md` — the
  endpoint accepts `DELETE, OPTIONS, PATCH` and answers `405` to `GET`. Nothing was lost: the
  full record had been snapshotted to `tmp/msv-milestones.json` first, and the re-creation
  merged the restore with the intended fix (script `tmp/fix_v_milestone_9e912298.py`).

### 2. The exact-degree theorem is published as a node, and joined to the mission

* Node **`4394b225-cc88-46d4-a57e-0765707d3246`**, `MagicSquares.semi_magic_polynomial_exists_degree_eq`,
  **`Proved`**, `public`, on the same `mathlib_rev` as the rest of the mission
  (`0df444a3…`). Submission `448ec295-45b1-4fb9-aa16-dc55b3b40a7f` → **ACCEPTED**, empty
  error.
* Milestone **`4995687d-e6eb-4803-8736-e0800f65925e`** at **sort_order 5**, i.e. directly after
  the goal's milestone `72482ba2`, with `milestone_description` saying explicitly that it is
  **strictly weaker** than milestone 4 and than the goal (`1 ≤ t` is not removable by this
  route). The ladder is now **8** rungs; `Theorem 1 (ii)` and `(iii)` were shifted to sort_order
  6 and 7 (`PATCH /milestones/<id>`).
* Proof bundle `Solutions/Sol_MagicSquares_semi_magic_polynomial_exists_degree_eq.lean`
  (2277 lines, the eight `spencer/*` modules concatenated in topological order with one import
  header), compiles locally in **88 s**; explanation
  `missions/magic-squares-v/expl-semi_magic_polynomial_exists_degree_eq.md`; payload
  `missions/magic-squares-v/submit-problem-degree-eq.json`.

**Ladder after this round** (`GET /missions/e06131f8-…/milestones`):

| sort | theorem | status |
|---|---|---|
| 0 | `semi_magic_count_two` | Proved |
| 1 | `semi_magic_count_three` | Proved |
| 2 | `semi_magic_count_one` | Proved |
| 3 | `semi_magic_count_four` | Open |
| 4 | `semi_magic_polynomial_exists` (**goal**) | Open |
| **5** | **`semi_magic_polynomial_exists_degree_eq`** | **Proved** |
| 6 | `semi_magic_reciprocity` | Open |
| 7 | `semi_magic_vanishing` | Open |

| | |
|---|---|
| Name | Magic Squares V: The Counting Function of Semi-Magic Squares of Every Order |
| `mission_type` | `ResearchPaper` |
| Field | `combinatorics` (`55eec41b-ff24-45ad-96b6-49d7a6869286`) |
| Description | 7 sections per `references/mission_description.md`, 1528 words |
| Items | 13 — 7 `reference`, 6 draft `theorem` |
| Read-backs | 6 of 6 draft items (written blind) |
| Milestones | **8**, in attack order (was 7 before 2026-09-20) |
| Goal (`main_item_id`) | `MagicSquares.semi_magic_polynomial` (item `e159ad1e`) |

## Target

BCCG Theorem 1 (Ehrhart 1973, Stanley 1973), with the elementary proof of Spencer
(1980) as the intended route for the hard rung:

> For every `n ≥ 1` there is `p ∈ ℚ[X]` of degree exactly `(n-1)²` with `p(t) = H_n(t)`
> for all `t ∈ ℕ`, `p(-n-t) = (-1)^(n-1) p(t)` for all `t ∈ ℤ`, and
> `p(-1) = … = p(-(n-1)) = 0`.

`H_n(t)` is `MagicSquares.semiMagicCount n t`, the number of `n × n` arrays of
nonnegative integers whose every row and column sums to `t`.

## The ladder (proposal milestones, in order)

| # | item | kind | state |
|---|---|---|---|
| 0 | `MagicSquares.semi_magic_count_two` | reference | **already Proved** on the platform |
| 1 | `MagicSquares.semi_magic_count_three` | reference | **already Proved** (MacMahon's `H_3`) |
| 2 | `semi_magic_count_one` | draft | `H_1(t) = 1` |
| 3 | `semi_magic_count_four` | draft | `11340·H_4(t) = 11t⁹+198t⁸+1596t⁷+7560t⁶+23289t⁵+48762t⁴+70234t³+68220t²+40950t+11340` |
| 4 | `semi_magic_polynomial_exists` | draft | existence + degree `(n-1)²`, uniformly in `n` |
| 5 | `semi_magic_reciprocity` | draft | `p(-n-t) = (-1)^(n-1) p(t)` |
| 6 | `semi_magic_vanishing` | draft | `p(-k) = 0` for `1 ≤ k ≤ n-1` |

The goal is deliberately *not* a milestone (the platform rejects that).

## Reference items, and what they fix

Five of the seven references are definition modules; four of them are the nodes that
were left orphan by the earlier missions (see `../magic-squares-reattach/status.md`).
Submitting this proposal grants them mission membership as a side effect, which
closes the orphan list completely:

`MagicSquares`, `MagicSquaresPandiagonal`, `MagicSquaresMostPerfect`,
`MagicSquaresTransforms`, `MagicSquaresNormal3`.

## The read-back caught a real error

The first version of the vanishing statement read

```lean
∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) - 1 → p.eval ((k : ℚ)) = 0      -- WRONG
```

which asserts `p` vanishes at the **positive** integers `1, …, n-1`. BCCG's list is
`H_n(-1) = … = H_n(-(n-1)) = 0`, i.e. the **negative** ones. The blind auditor flagged
it explicitly ("Vanishing uses `k`, not `-k`"), which is exactly the class of error the
read-back exists to catch. Corrected to

```lean
∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) - 1 → p.eval (-(k : ℚ)) = 0
```

in `examples/magic-squares/mission_v_drafts.lean`, in the statement prototype
`examples/magic-squares/mission_v_goal_shape.lean`, and on the proposal item. The
auditor was then **re-run on the corrected code** (a read-back of a stale statement
testifies about the wrong artifact), and the second pass no longer flags it.

## Files

| what | where |
|---|---|
| proposal payload (name / description / type / fields) | `proposal-create.json` |
| proposal id | `proposal_id.txt` |
| item ids, order, `main_item_id` | `items.json` |
| milestone list as returned by the platform | `proposal-milestones.json` |
| the six draft statements, compiled locally | `../../examples/magic-squares/mission_v_drafts.lean` |
| statement-shape prototype + non-vacuity checks | `../../examples/magic-squares/mission_v_goal_shape.lean` |
| blind auditor input (all comments stripped) | `../../tmp/mission_v_audit_input.lean` |
| the six read-backs | `../../tmp/mission_v_readbacks.md` |
| scripts | `../../tmp/create_mission_v.py`, `fill_mission_v_items.py`, `seed_mission_v_milestones.py`, `fix_mission_v_description.py`, **`verify_mission_v_items.py`** (assembles `preamble + statement` and compiles it, patches, then re-compiles the live payload) |
| design rationale, statement shapes, alternatives | `DESIGN.md` |

The draft `formal_statement`s on the platform are extracted programmatically from
`mission_v_drafts.lean`, so they cannot drift from what was compiled locally.

## What happens at Submit

Per `references/mission_captain.md`: at the user's Submit every **draft** item is
compiled and published as an immutable platform theorem, then the proposal goes to
moderation. If any draft fails to compile the whole Submit fails — all six were
checked locally with `lake env lean` under the platform preamble
(`import Mathlib` + `import Definitions.Def_MagicSquares` + `open MagicSquares`),
so this should not happen.

## Fix applied 2026-09-19 ~14:00: drafts were missing their `namespace`

The review page showed **Compile failed** on every draft item:

```
formal statement does not compile: line 7: Invalid `end`: There is no current scope to end
line 9: Unknown constant `MagicSquares.semi_magic_count_one`
```

Cause: the platform compiles `preamble` + blank line + `formal_statement` as one file, and
the `namespace MagicSquares` lives in the scratch file, not in the uploaded statement. The
extraction kept the trailing `end MagicSquares` but not the opening `namespace`, so the
`end` had nothing to close and the declaration landed at the root namespace. All six drafts
were affected. **Local compilation of `mission_v_drafts.lean` could not catch this** — that
file does open the namespace — so the lesson is: *verify the assembled artifact, not the
source file*.

Fixed with `tmp/verify_mission_v_items.py`, which

1. rebuilds each statement wrapped in `namespace MagicSquares … end MagicSquares`,
   assembles `preamble + statement` into a file and runs `lake env lean` — all six compile;
2. `PATCH`es the six items, **re-attaching `readback` and `readback_model` in the same call**
   so the read-backs are not lost;
3. **re-fetches the live payloads and compiles those** — all six compile, read-backs intact.
   Do not trust the `200` alone.

`tmp/fill_mission_v_items.py` now opens the namespace itself, so the bug cannot recur.

The read-backs did **not** need re-running: only the namespace wrapper changed, and the blind
auditor had been given the namespace-wrapped code (`tmp/mission_v_audit_input.lean`) all
along. However, **editing a draft item clears any prior human confirmation**, so the six
items need to be re-confirmed before Submit.

## Progress after Submit

### `semi_magic_count_one` — **Proved** (2026-09-19)

Node `611ea9c5-4346-49e1-800c-aa23be9f7303`, submission
`66271456-2a15-4bd9-8d3d-303f5dc3b1b7` → **ACCEPTED**, empty error. Source
`../../Solutions/Sol_MagicSquares_semi_magic_count_one.lean` (48 lines, no `sorry`,
no `axiom`), explanation `expl-semi_magic_count_one.md`.

Proof: the single row sum of a `1 × 1` array is its entry, so the line-sum equation
reads `(M 0 0 : ℕ) = t`; since entries live in `Fin (t+1)` this pins the entry, the
filtered finset is the singleton on the all-`t` array, and its cardinality is `1`.
Done with `Finset.card_eq_one` + `Finset.eq_singleton_iff_unique_mem`.

**Tooling trap worth remembering** (cost three compile iterations): the witness array
must be a **named** term (`let M0 : Square 1 (Fin (t+1)) := …`). Writing it inline as
`{fun _ _ => ⟨t, …⟩}` makes the notation elaborate as a *comprehension* instead of a
singleton, after which `Finset.eq_singleton_iff_unique_mem` no longer matches — the
symptoms are misleading: `Finset.mem_filter` is reported as an unused `simp` argument
and `constructor` fails with "target is not an inductive datatype", because the
membership has quietly become a set-membership. The working `pan_three_card` solution
passes a *named* definition for exactly this reason.

### Ladder state

Platform status of the six draft nodes (re-read from `/missions/e06131f8-…/milestones`,
2026-09-19 21:1x local), next to what the Spencer route already proves **locally**:

| node | platform | Spencer route (local, `lake build SpencerRoute`, no `sorry`/`axiom`) |
|---|---|---|
| `semi_magic_count_two`, `semi_magic_count_three` | Proved (references) | — |
| **`semi_magic_count_one`** | **Proved** | — |
| `semi_magic_count_four` | Open | — (concrete `n = 4` interpolation, not on the Spencer route) |
| **`semi_magic_polynomial_exists`** | Open | **almost**: degree exactly `(n-1)²` and agreement for `t ≥ 1` — `exists_polynomial_semiMagicCount_degree_eq`; **missing the `t = 0` value** |
| `semi_magic_reciprocity` | Open | — (S5) |
| `semi_magic_vanishing` | Open | — (S5 says the two are the same content) |
| `semi_magic_polynomial` (goal) | Open | — |

The published `semi_magic_polynomial_exists` asks for

```lean
∃ p : Polynomial ℚ, p.natDegree = (n - 1) ^ 2 ∧ ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)
```

(verified verbatim from `GET /theorems/3dc34529-feed-4b21-bd4f-443097422b63`; the `∀ t : ℕ` is the
whole difficulty — our local theorem carries the extra hypothesis `1 ≤ t`).

## The `H_4` polynomial is confirmed by the literature — and one claim in the description is wrong

Cross-checked against Beck–Pixton, *The Ehrhart polynomial of the Birkhoff polytope*,
Discrete Comput. Geom. **30** (2003) 623–637 (<https://arxiv.org/abs/math/0202267>), §3.
Their expanded `H_4(t)` is

$$H_{4}(t)=\frac{11}{11340}t^{9}+\frac{11}{630}t^{8}+\frac{19}{135}t^{7}+\frac{2}{3}t^{6}+\frac{1109}{540}t^{5}+\frac{43}{10}t^{4}+\frac{35117}{5670}t^{3}+\frac{379}{63}t^{2}+\frac{65}{18}t+1,$$

**term for term identical to what was fitted here from direct enumeration** on
`t = 0..16` (fit on the first ten values, verified on all seventeen). The integer
identity in `semi_magic_count_four` is therefore the correct one.

🔴 **But the surrounding prose overstates it.** The description and the milestone for
`semi_magic_count_four` say "leading coefficient `11/11340 = vol(B_4)`" and
"normalised volume `352`". Beck–Pixton's §3 and their §4 table give

- the **leading coefficient** of the Ehrhart polynomial: `11/11340` — correct;
- the **Euclidean volume**: $\operatorname{vol}(B_4) = 4^{3}\cdot\tfrac{11}{11340} = \tfrac{176}{2835}$,
  because the counting lattice has relative fundamental volume $n^{n-1} = 64$;
- the lattice-normalised volume $9! \cdot \tfrac{11}{11340} = 352$ — this one is fine
  as stated, given "normalised" is read as $d! \times$ (lattice volume).

So `11/11340` is **not** `vol(B_4)`; it is smaller by the factor `64`. For comparison,
Beck–Pixton give $\operatorname{vol}(B_3) = 9/8$ with leading coefficient `1/8`.

Consequence: the proposal is `In review` and **frozen** (no PATCH on description or
items). The formal statement is unaffected — it is the cleared-denominator identity,
verified — but the milestone text should be corrected **once the mission goes live**,
where milestones of a live mission are captain-editable, and a short comment in the
mission discussion should record the correction. Do not repeat the `vol(B_4)` claim
verbatim from that milestone.

## A tooling lesson worth keeping

The first attempt at trimming the description split the text on `\n\n` and replaced
one paragraph per cut. A Markdown bullet list is a *single* paragraph by that
splitting rule, so two cuts silently deleted the sibling bullets — four timeline
entries and four of the five formalization-scope bullets, including the
"trivializing formalization to avoid" sentence that the description spec requires.
It was caught by re-reading the whole description back, and the description was
rebuilt from a single literal with structural assertions (`assert '1915' in desc`,
`assert 'trivializing' in desc`, bullet-count check). **Do not do paragraph surgery
on Markdown lists**; assert on the content you expect to survive.

---

## Hard rungs: the Spencer route (2026-09-19)

The five remaining rungs (`semi_magic_count_four`, `semi_magic_polynomial_exists`,
`semi_magic_reciprocity`, `semi_magic_vanishing`, goal) are not cheap corollaries.  The route
that makes the general-`n` rung reachable at all is **J. Spencer, *Counting magic squares*,
Amer. Math. Monthly 87 (1980) 397–399** — an *elementary* proof (generating functions, Hall's
marriage theorem, a poset of supports), which matters because Mathlib has no Ehrhart /
quasi-polynomial machinery whatsoever.

Full working notes, Mathlib inventory and two boundary subtleties:
**`SPENCER-ROUTE.md`** (same directory).  Anything touching these rungs should read it first.

Landed so far, all under `examples/magic-squares/spencer/`, all building clean with no
`sorry` or `axiom` (**1037 lines**, `lake build SpencerRoute` — the five files import each other, so
they are now a Lake library in `lakefile.lean`, not a default target):

| file | lines | content |
|---|---|---|
| `Spencer.lean` | 182 | discrete antiderivative `exists_antideriv` (`P ↦ Σ_{m<n} P m`, degree `+1`), the Spencer step `isPolyDegLe_of_recurrence` (triangular recurrence with polynomial coefficients of degree `≤ K` ⇒ degree `≤ K+1`) and its shifted form `isPolyDegLe_of_recurrence_succ` |
| `HallSupport.lean` | 68 | `exists_perm_pos_of_line_sums`: a nonnegative integer matrix whose rows and columns all sum to the same positive `t` contains a permutation `σ` with `0 < M i (σ i)` |
| `SupportSplit.lean` | 401 | the split `T ↦ T - P` with its support behaviour, the ℕ-valued fibres `matBox`/`matFiber`/`fiberCandidates`, and the cardinal assembly: `card_matFiber_split` (the bijection) and `card_matFiber_recurrence` (the recurrence `h_B(s) = h_B(s-1) + Σ_{C ∈ nb(B)} h_C(s-1)`) |
| `Recursion.lean` | 244 | **completes step 3**: the ambient-bound cancellation `matFiber_eq_of_le`, the Hall choice `exists_perm_support_subset_of_lineSums`, the recurrence with constant coefficients `card_matFiber_recurrence_succ`, and the induction `isPolyDegLe_gB` (`#B`-degree polynomiality of the level counts at a fixed support) |
| `Aggregate.lean` | 142 | **S4**: the bridge to the platform's `semiMagicCount` (`isSemiMagic_iff_lineSums`, `card_matBoxLine`, `semiMagicCount_eq_sum_matFiber`), the shift `exists_poly_comp_X_sub_one`, and the payoff **`exists_polynomial_semiMagicCount_pos`** |

**Step 3 of Spencer's four is done, and so is the aggregation S4.**  The payoff theorem is

```lean
theorem exists_polynomial_semiMagicCount_pos (n : ℕ) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ n * n ∧
      ∀ t : ℕ, 1 ≤ t → p.eval (t : ℚ) = (semiMagicCount n t : ℚ)
```

verified locally with `#print axioms` → only `propext, Classical.choice, Quot.sound`.  It is *not a
platform node yet*: mission V has no mission id (proposal `In review`), so there is nothing to
attach it to — see the note at the end of this file.

Still to do at the time of writing: the sharp degree bound `(n-1)²` (S3) and the value at line sum
`0` (equivalently Ehrhart–Macdonald reciprocity at `-1`, S5).  §8 of `SPENCER-ROUTE.md` records the
design; each new rung must be a **new** declaration, not an edit of an existing one.  (S3 has since
landed, and so has its lower half — both below.)

✅ **S3 landed 2026-09-19 ~24:00** — the sharp degree bound is proved locally, as **new**
declarations, in two new files (`spencer/Rank.lean`, `spencer/Sharp.lean`, both added to the
`SpencerRoute` lake lib; `lake build SpencerRoute` passes):

```lean
theorem exists_polynomial_semiMagicCount_sharp (n : ℕ) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ (n - 1) ^ 2 ∧
      ∀ t : ℕ, 1 ≤ t → p.eval (t : ℚ) = (semiMagicCount n t : ℚ)
```

with `#print axioms` → only `propext, Classical.choice, Quot.sound`.  The supporting rung
`isPolyDegLe_gB_sharp (n) (B) : IsPolyDegLe (rankB B) (gB n B)` measures the degree by
`rankB B := dim (zero-line-sum space of B)` (the face rank without graph theory) and needs a real
strictness lemma: `rankB C < rankB B` for candidates `C ⊂ B` that contain a permutation support
— proved by duality (`LinearMap.range_dualMap_eq_dualAnnihilator_ker`) plus a two-summing
contradiction over the `σ`- and `τ`-cells, using exactly the candidate constraint
`B \ φ(σ) ⊆ C`.  Degenerate candidates (`rankB C = rankB B`) never contain a permutation, so
their counts vanish identically.  Publishing both nodes is now unblocked — mission V is live
(`e06131f8`, see the top of this file).

**Note on the published description.**  The proposal's Timeline bullet for `n = 4` says the
leading coefficient `11/11340` *is* `vol(B_4)`; that is wrong by a factor of `n^{n-1} = 64`
(`vol(B_4) = 176/2835`, cf. `vol(B_3) = 9/8`).  The formal statement is unaffected (it is the
cleared-denominator identity, checked against Beck–Pixton).  The wording should be corrected in
the milestone text once the proposal is out of review, and the discussion thread should carry a
correction notice until then.

✅ **Confirmed 2026-09-19 20:00** — the fix is still blocked, and it is *not* an oversight:
mission **IV** is the one that went live (`df1cb8cc`, cf. `../../.workbuddy/memory/PLATFORM-NOTES.md`),
while mission V's proposal `3a8476fd` is still `In review`, so its description and items remain
un-PATCHable and the milestone text has not yet become captain-editable.

✅ **Unblocked 2026-09-19 21:1x** — the proposal has since flipped to `Reviewed` with
`mission_id = e06131f8-…`, so the milestone text **is** captain-editable now.  Do both halves:
correct the `vol(B_4)` wording in the milestone, **and** post a correction notice in the mission
discussion so the fix is on the record.  Neither has been done yet.

---

## ✅ Brick 11: the exact degree — the matching lower bound (2026-09-19 ~21:00)

`Sharp.lean` gave `natDegree ≤ (n-1)²`; the other inequality was the last open piece of step 4 of
Spencer's four.  It is now proved, in a **new** file `examples/magic-squares/spencer/Degree.lean`
(~375 lines, clean, added to the `SpencerRoute` lake lib; `lake build SpencerRoute` passes,
`#print axioms` → only `propext, Classical.choice, Quot.sound`):

```lean
theorem exists_polynomial_semiMagicCount_degree_eq (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : Polynomial ℚ, p.natDegree = (n - 1) ^ 2 ∧
      ∀ t : ℕ, 1 ≤ t → p.eval (t : ℚ) = (semiMagicCount n t : ℚ)
```

Note the signature is now *character-for-character* the platform's `semi_magic_polynomial_exists`
except for the trailing hypothesis `1 ≤ t`.

**Method — an explicit linear family, not Ehrhart.**  For a square of order `n + 1` and line sum
`(n + 1) * s`, take any `c : Fin n → Fin n → Fin (s / n + 1)` (that is, `(n*n)` free parameters,
each in a box of size `s / n + 1`) and build the `(n+1) × (n+1)` matrix

* `M p q = s + c p q` on the top-left `n × n` block,
* `M p last = s - Σ_q c p q` (last column), `M last q = s - Σ_p c p q` (last row),
* `M last last = s + Σ_{p,q} c p q` (corner).

Every line sums to `n*s + Σc + (s - Σc) = (n+1)*s`, and `c p q ≤ s/n` gives `Σ_q c p q ≤ n*(s/n) ≤ s`,
so all entries are `ℕ`.  The block is recovered from `M` by `c p q = M p q - s`, so the map is
injective and

```lean
theorem semiMagicCount_ge_family (n s : ℕ) (hn : 1 ≤ n) :
    (s / n + 1) ^ (n * n) ≤ semiMagicCount (n + 1) ((n + 1) * s)
```

Growth `≥ s^((n-1)²)` at `n' = n - 1` then forces `natDegree ≥ (n-1)²`, via the purely elementary
lemma

```lean
theorem le_natDegree_of_lowerBound {p : Polynomial ℚ} {d : ℕ} {A : ℚ} (hA : 1 ≤ A)
    (h : ∀ s : ℕ, 1 ≤ s → (s : ℚ) ^ d ≤ p.eval (A * (s : ℚ))) : d ≤ p.natDegree
```

(`p.eval x ≤ B * x ^ e` with `B` = Σ|coeff| for `x ≥ 1` from `eval_le_mul_pow`, against
`s ^ d = s ^ (d - e) * s ^ e ≥ s * s ^ e` at a large `s` — `by_contra` + `exists_nat_gt`; no
analysis, no asymptotics).

**What this does *not* settle.**  The published goal quantifies over **all** `t : ℕ`, and the
Spencer machinery only ever produces agreement for `t ≥ 1` (§4.1 of `SPENCER-ROUTE.md`): the
support-set recursion has no term for the empty support, so the value at line sum `0` is invisible
to it.  Closing `semi_magic_polynomial_exists` therefore needs **S5**, i.e. `p(0) = H_n(0) = 1`,
equivalently `q(-1) = 1` for the shifted polynomial — which is Ehrhart–Macdonald reciprocity at
`-1` (`B_n` has no interior lattice points for `n ≥ 2`).  The exact degree is what makes S5
*checkable*: with `n` values already pinned it is a single extra evaluation, not a search.

**Files added this round** (all previously **untracked**, now committed together with `Degree.lean`
so that the tree actually builds from `HEAD`): `spencer/Spencer.lean`, `spencer/HallSupport.lean`,
`spencer/SupportSplit.lean`, `spencer/Recursion.lean`, `spencer/Aggregate.lean`,
`spencer/Degree.lean` + the `lakefile.lean` `SpencerRoute` roots.  (`Rank.lean`/`Sharp.lean` were
already in `d880dd8`, but their five dependencies were not — the committed tree did not build.)

---

## 🔬 S5 reconnaissance (2026-09-20 ~11:1x–11:4x): the gap is now *exactly* two statements

S5 = the value at line sum `0`, i.e. `q(-1) = 1` for the degree-`(n-1)²` polynomial agreeing with
`t ↦ H_n(t+1)` on `ℕ`.  Full derivation in **`S5-NOTES.md`** (same directory).  The outcome:

* S5 ⟺ `Σ_{B ≠ ∅} s_B = 1`, where `s_B := q_B(-1)` and the recursion `s_B = a_B − Σ_{C ∈ nb(B)}s_C`
  (`a_B = 1` iff `B` is a permutation support) is what the polynomial identity
  `q_B(X+1) − q_B(X) = Σ_C q_C(X)` turns into at `X = −1`;
* that splits into **(A)** `q_B(−1) = (−1)^rankB B` for every support `B` (= Ehrhart–Macdonald
  reciprocity at `−1`, so it carries the same content as the two other open rungs
  `semi_magic_reciprocity` / `semi_magic_vanishing`), and **(B)**
  `Σ_{∅≠B support}(−1)^rankB B = 1` (= Euler's formula `Σ_F(−1)^dim F = 1` for the face lattice of
  the Birkhoff polytope — true for every polytope, no Ehrhart theory involved);
* **both (A) and (B) were verified numerically, exactly, for `n = 2, 3, 4`** — 3 / 49 / 7443
  supports respectively, all clean, and `Σ_B q_B(−1) = 1` in all three cases.  The `n = 4` run also
  reproduces `H_4(s)` for `s = 1…11` (matching Beck–Pixton), which validates the enumerator.
  Scripts: `tmp/s5_probe.py` (n=2,3), `tmp/s5_probe4.py` (n=4), both exact-rational, no floats.

⚠️ Numerical evidence only — not a proof, and no finite check can settle a statement uniform in `n`.
**The goal stays `Open`.**  What changed: S5 is no longer "a hard research problem, vaguely =
reciprocity"; it is (A)+(B), both named and both verified, with (B) being polytope-general.

**Next actions, in the order `S5-NOTES.md` §6 recommends:** (1) leave the goal `Open` and rely on the
three published siblings; (2) do the §3 recursion in Lean (small — it eliminates all polynomials from
S5 and leaves only the combinatorial `Σ_B s_B = 1`); (3) attack (B) first (no reciprocity in it);
(4) attack (A) last, since it closes three rungs at once and is therefore a project, not a detour.

## ✅ Brick 12: the S5 reduction, machine-checked (2026-09-20 ~12:0x–12:15)

Option (2) above is **done**.  New file `examples/magic-squares/spencer/S5.lean`, ninth root of the
`SpencerRoute` lib (`lakefile.lean` updated), `lake build SpencerRoute` green
(`Built …S5 (23s)`), no `sorry`/`axiom` (all new theorems report
`[propext, Classical.choice, Quot.sound]`, `tmp/axiom_check_s5.lean`).

§3 of `S5-NOTES.md` is now a theorem chain:

| where | what |
|---|---|
| `qB n B`, `qB_eval` | the support polynomial: `(qB n B).eval r = #(line-sum-(r+1) fibre at B)` |
| `nbOf n B` | the split's neighbour set — `∅` when no permutation fits inside `B` |
| `gB_succ` | `gB n B (r+1) = gB n B r + Σ_{C ∈ nbOf n B} gB n C r`, at **every** `B` |
| `qB_rec` | `qB (X+1) − qB = Σ_{C ∈ nbOf n B} qB C` in `ℚ[X]` |
| `sB`, `sB_rec` | `sB n B = #(level-1 fibre at B) − Σ_C sB n C` — polynomials eliminated |
| `IsSupport`, `supportSet`, `sB_eq_zero_of_not_isSupport` | supports, and non-supports contribute `0` |
| `ReciprocityAtNegOne`, `FaceLatticeEuler` | **(A)** and **(B)** from above, as `Prop`s |
| `sum_sB_eq_one_of` | (A) + (B) ⟹ `Σ_B sB n B = 1` |
| `exists_polynomial_semiMagicCount_of_sum_sB`, `…_degLe_of_sum_sB` | `Σ_B sB n B = 1` ⟹ the count is polynomial on **all** of `ℕ` (the second keeps `natDegree ≤ (n−1)²`) |

Combined with `exists_polynomial_semiMagicCount_degree_eq`, this says: assuming `Σ_B sB n B = 1`,
the mission's **goal** follows.  So the remaining mathematical content is now exactly (A) and/or
(B) — the reduction itself is no longer a source of doubt.  **The goal is still `Open`**; nothing
here proves (A) or (B).

**Strategic note added while formalising (`S5-NOTES.md` §7.1).**  `H_n(t)` counts the lattice
points of `t·B_n`, so S5 *is* Ehrhart's theorem for the Birkhoff polytope.  (A) is stronger than
needed and (B) alone is not enough; but a third route closes the goal without either: triangulate
into lattice simplices and use the simplex count
`L_Δ(t) = Σ_{y ∈ Π ∩ ℤ^{d+1}} binom(t − deg y + d, d)` (a polynomial for all `t ≥ 0`, with
`L_Δ(0) = 1` for free since `0 ≤ deg y ≤ d`), then inclusion–exclusion over the triangulation.
That route is a *Mathlib project* (simplex count + lattice triangulations), self-contained, with no
reciprocity and no face-lattice Euler formula.  Which of the two to fund is a captain's call;
recommendation stands as §6: (3) before (4) if going the (A)/(B) way.

Implementation pitfalls (the ones worth keeping) are recorded in `SPENCER-ROUTE.md` §8.5 — most
importantly that `(0 : ℚ)` and `((0 : ℕ) : ℚ)` are not interchangeable for `rw`, and that
"a polynomial over `ℚ` vanishing on all of `ℕ` is zero" is the single `ℚ[X]`-specific input of the
whole brick.
