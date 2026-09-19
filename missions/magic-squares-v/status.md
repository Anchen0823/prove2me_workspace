# Magic Squares V — proposal status

Last updated: 2026-09-19 (Asia/Shanghai).

**Proposal id `3a8476fd-e093-414d-a8d8-e020d2466a57`, status `In review`** — Submitted by the user
on 2026-09-19 ~13:47; the six draft items were published as platform nodes (all `Open`, see
`published-nodes.json`) and `semi_magic_count_one` is already **Proved**.  **Mission IV** went live
as `df1cb8cc`; mission V itself is *not* live yet, which is why the milestone text is still frozen
(see the note at the end of this file).

| | |
|---|---|
| Name | Magic Squares V: The Counting Function of Semi-Magic Squares of Every Order |
| `mission_type` | `ResearchPaper` |
| Field | `combinatorics` (`55eec41b-ff24-45ad-96b6-49d7a6869286`) |
| Description | 7 sections per `references/mission_description.md`, 1528 words |
| Items | 13 — 7 `reference`, 6 draft `theorem` |
| Read-backs | 6 of 6 draft items (written blind) |
| Milestones | 7, in attack order |
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

| node | status |
|---|---|
| `semi_magic_count_two`, `semi_magic_count_three` | Proved (references) |
| **`semi_magic_count_one`** | **Proved** |
| `semi_magic_count_four`, `semi_magic_polynomial_exists`, `semi_magic_reciprocity`, `semi_magic_vanishing` | Open |
| `semi_magic_polynomial` (goal) | Open |

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

Still to do: the sharp degree bound `(n-1)²` via the face rank `ρ(B) = |B| - v(B) + c(B)` (S3) and
the value at line sum `0` (equivalently Ehrhart–Macdonald reciprocity at `-1`, S5).  §8 of
`SPENCER-ROUTE.md` records the design of what was done and the open questions for S3/S5;
when S3 lands it must be a **new** declaration, not an edit of this one.

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
their counts vanish identically.  Publishing both nodes is still blocked on mission V going
live (`3a8476fd` `In review`).

**Note on the published description.**  The proposal's Timeline bullet for `n = 4` says the
leading coefficient `11/11340` *is* `vol(B_4)`; that is wrong by a factor of `n^{n-1} = 64`
(`vol(B_4) = 176/2835`, cf. `vol(B_3) = 9/8`).  The formal statement is unaffected (it is the
cleared-denominator identity, checked against Beck–Pixton).  The wording should be corrected in
the milestone text once the proposal is out of review, and the discussion thread should carry a
correction notice until then.

✅ **Confirmed 2026-09-19 20:00** — the fix is still blocked, and it is *not* an oversight:
mission **IV** is the one that went live (`df1cb8cc`, cf. `../../.workbuddy/memory/PLATFORM-NOTES.md`),
while mission V's proposal `3a8476fd` is still `In review`, so its description and items remain
un-PATCHable and the milestone text has not yet become captain-editable.  Re-check
`GET /mission-proposals/3a8476fd-e093-414d-a8d8-e020d2466a57` for `status` before retrying; when it
flips, do both halves (milestone wording **and** a correction comment in the discussion).
