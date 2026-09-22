# Magic Squares V live audit — 2026-09-20

## Scope and evidence

This is a read-only platform audit.  The live API evidence is in the JSON files in
this directory; `live-milestones.json` is the authoritative list rather than the
older local handoff.  The live mission is
`e06131f8-1bf5-47c4-b8f4-507f107269e0` (proposal
`3a8476fd-e093-414d-a8d8-e020d2466a57`, status `Reviewed`).

The platform environment used by every node examined here is Mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474` on
`leanprover/lean4:v4.33.1`; it agrees with the workspace `lean-toolchain` and
`lakefile.lean`.

## Live milestones

| order | milestone id | theorem id | Lean name | status |
| ---: | --- | --- | --- | --- |
| 0 | `75d1ded5-7405-40c6-b0fc-d7981a085145` | `86515ed9-6bd4-4484-a3d2-a1be23ce7ac9` | `MagicSquares.semi_magic_count_two` | Proved |
| 1 | `c0b981fa-403b-495e-8b80-195a47d06452` | `55e2191d-be25-4e6d-af7a-4635a34e5c63` | `MagicSquares.semi_magic_count_three` | Proved |
| 2 | `3e3c2d2d-4865-41dc-9389-c344b7cdd8ab` | `611ea9c5-4346-49e1-800c-aa23be9f7303` | `MagicSquares.semi_magic_count_one` | Proved |
| 3 | `c791e322-27f8-49d9-bdcd-cd9120a5fe8c` | `f85e8a07-5809-4c91-84a4-cea1cb2a7939` | `MagicSquares.semi_magic_count_four` | **Open** |
| 4 | `72482ba2-7bc1-4eff-85bd-d8e380234b47` | `3dc34529-feed-4b21-bd4f-443097422b63` | `MagicSquares.semi_magic_polynomial_exists` | **Open** |
| 5 | `4995687d-e6eb-4803-8736-e0800f65925e` | `4394b225-cc88-46d4-a57e-0765707d3246` | `MagicSquares.semi_magic_polynomial_exists_degree_eq` | Proved |
| 6 | `e980f5b0-9805-429b-bad3-01d05405b88d` | `32ea160a-bf6c-4a8f-90f7-31289a3d3ba3` | `MagicSquares.semi_magic_reciprocity` | **Open** |
| 7 | `d1f47653-3609-4bf7-b745-620afbfc195e` | `2b98befc-35ff-4cd0-be18-2536bf8adae8` | `MagicSquares.semi_magic_vanishing` | **Open** |

The separate mission goal is also **Open**:
`a8fa7ac8-321b-492a-9e96-d5303081a54f`,
`MagicSquares.semi_magic_polynomial`.  Its live open-leaf query returns only
itself (`closability: 0`), so it has no published proof-sketch children.

## Exact primary target

The next proof must have a top-level `theorem solution` of exactly this type:

```lean
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : Polynomial ℚ,
      p.natDegree = (n - 1) ^ 2 ∧
        ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ) := by
  -- no sorry
```

This is the exact formal statement of live theorem
`3dc34529-feed-4b21-bd4f-443097422b63`.  It is the recommended immediate
target: it is strictly stronger than the accepted Spencer theorem only at
`t = 0`.  The accepted, public supporting node
`4394b225-cc88-46d4-a57e-0765707d3246` provides the same existential and
exact degree with an added `1 ≤ t` premise.  Its interface is
`MagicSquaresSpencer.exists_polynomial_semiMagicCount_degree_eq n hn`.

The remaining open statements are independent of the positive-line-sum
closure:

```lean
-- f85e8a07-5809-4c91-84a4-cea1cb2a7939
theorem solution (t : ℕ) :
  11340 * semiMagicCount 4 t =
    11 * t ^ 9 + 198 * t ^ 8 + 1596 * t ^ 7 + 7560 * t ^ 6 +
      23289 * t ^ 5 + 48762 * t ^ 4 + 70234 * t ^ 3 +
      68220 * t ^ 2 + 40950 * t + 11340 := by
  -- no sorry

-- 32ea160a-bf6c-4a8f-90f7-31289a3d3ba3
theorem solution (n : ℕ) (hn : 1 ≤ n) (p : Polynomial ℚ)
    (hp : ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)) :
    ∀ t : ℤ, p.eval (((-(n : ℤ) - t : ℤ) : ℚ)) =
      (-1 : ℚ) ^ (n - 1) * p.eval ((t : ℤ) : ℚ) := by
  -- no sorry

-- 2b98befc-35ff-4cd0-be18-2536bf8adae8
theorem solution (n : ℕ) (hn : 1 ≤ n) (p : Polynomial ℚ)
    (hp : ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)) :
    ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) - 1 → p.eval (-(k : ℚ)) = 0 := by
  -- no sorry
```

## Duplicate-work checks

The four Open milestone theorem submission lists are all empty: no pending,
failed, or accepted proof submission is currently attached.  The histories for
the order-four, polynomial-existence, and vanishing milestones have no events,
so there is no captain-rejected route to avoid.  The live API returned
`Milestone not found` for the stated reciprocity history id despite listing
that same id in the current mission response; this is recorded verbatim in
`history-semi-magic-reciprocity.json` and should be treated as an endpoint/data
inconsistency, not evidence of a rejected approach.

The live decomposition records for the three structural Open nodes contain
only the `MagicSquares` definition.  Thus the accepted Spencer node is
mathematical and local-code support, not yet a platform dependency edge.

## Local baseline

`lake build SpencerRoute` first failed through the elan launcher because its
self-update check could not reach `release.lean-lang.org`.  Retrying the same
target through the installed pinned toolchain executable
`C:\\Users\\anche\\.elan\\toolchains\\leanprover--lean4---v4.33.1\\bin\\lake.exe`
succeeded: **8,716 jobs**, exit code **0**.  The log contains only existing
linter/deprecation warnings and is saved as `spencerroute-build.log`.

## Submission gate for the proposed closure

Do not publish from this audit.  When the closed-support modules are ready,
assemble a standalone file whose only platform imports are `Mathlib` and
`Definitions.Def_MagicSquares`, defines a top-level `theorem solution` matching
the primary target verbatim, contains no `sorry`/`admit`, and does not import
`Theorems.Thm_3dc34529-feed-4b21-bd4f-443097422b63`.  Compile that assembled
file locally on the pinned environment before any later verification request.
