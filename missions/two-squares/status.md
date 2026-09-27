# Mission: Equal Sums of Two Squares — Parametrization and Infinite Primitive Families

Last updated: 2026-09-26 20:25 GMT+8

## Objective and platform state

- **Platform proposal: `1c96fbbb-cfea-4ad7-b9bb-44abccb2ad78`** — created 2026-09-26,
  `visibility = public`, `mission_type = ResearchPaper`, field Number Theory. Title: *Equal
  Sums of Two Squares: Parametrization and Infinite Primitive Families*. 13 items + 12
  milestones.
- **Status: `In review`, `mission_id = null`** (awaiting moderator approval). The human clicked
  "Submit Proposal" on 2026-09-26 19:5x, which compiled all 13 drafts into immutable theorems;
  `theorem_ids resolved: 13/13` (read back 2026-09-26 20:2x).
- **All 13 submissions are `ACCEPTED`** — every item including the goal is now `Proved` on the
  platform. Submission ids and hashes: `platform/submissions-receipt.json`. Read back from
  `GET /submissions/<id>`, never from a log.
- Note (correcting an earlier belief recorded in the skill): the platform **does** accept
  submissions while a proposal is `In review`, i.e. before moderator approval. That is what
  `--submit --allow-pre-approval` does.
- No live mission yet in the account's mission list: `GET /missions?limit=200` (2026-09-26,
  before submit) returned 100 missions, none with "square(s)" in `name` or `slug` other than an
  unrelated ML mission. The proposal has not been approved into a mission at the time of writing.
- Root theorem: `EqualTwoSquares.complete_parametrization`,
  theorem id `5e2fbf33-6086-49c4-a894-d49d3616bc96` — **Proved** (submission accepted).
- Platform status and time verified: `In review`, 13/13 theorem ids, 13/13 accepted proofs,
  read back 2026-09-26 20:2x.
- Active target name / ID: local `examples/two-squares/{Identity,Family}.lean`; platform files
  under `missions/two-squares/platform/`.
- Open frontier: **none of the six mission objectives remains open.** All 13 items of the
  proposal are proved, Objectives 1–6 included.
- Lean toolchain: `v4.33.1` (elan).
- Mathlib revision: `0df444a360eaa60ab8c11dca51a86af692955474`.

## Source and strategy

The mission text asks for six objectives; only the first three are in scope now.

- **Objective 1** (four-parameter identity). Done. Stated over an arbitrary `CommRing` and derived
  from the two Brahmagupta–Fibonacci forms rather than re-expanded, so the file has exactly two
  `ring` calls and the identity visibly says "both sides are the same product".
- **Objective 2** (explicit family). Done. The identity is stated for **all** integers `n`
  (pure polynomial identity, no hypothesis); positivity and distinctness are separated out and
  funnelled through one strict chain, see below.
- **Objective 3** (inequivalent primitive patterns). Done, in the "injective parametrisation"
  form the mission recommends, plus two cheap extras: infinitude of the pattern set and
  `family_scaling_trivial`.
- Relevant prior submissions, audits, rejected approaches: none — this is a new mission for the
  workspace. Related Mathlib infrastructure surveyed: `GaussianInt` is an abbreviation for
  `zsqrtd (-1)` with notation `ℤ[i]`; its norm field is **`norm`** (not `normSq`), with
  `Zsqrtd.norm_mul`, `GaussianInt.norm_eq_zero`, `norm_pos`, `natAbs_norm_eq`. Gcd/divisibility
  toolkit confirmed for Objective 5: `Int.gcd`, `Int.gcd_eq_natAbs`,
  `Int.gcd_ediv_gcd_ediv_gcd`, `Nat.coprime_div_gcd_div_gcd`, `Nat.Coprime.dvd_of_dvd_mul_left`,
  `Nat.Coprime.dvd_of_dvd_mul_right`, `Nat.Coprime.mul_dvd_of_dvd_of_dvd`, `IsCoprime.*`.
  Parity: `Int.even_or_odd`, `Int.emod_two_eq_zero_or_one`, `Int.even_sub`, `Odd.pow`
  (NB: **no `Even.pow`** in this pin).
- Planned proof or decomposition: see "Next action".

### Design note: how "positive and pairwise distinct" is formalised

Everything goes through one theorem, `TwoSquares.explicit_family_chain`:

```
1  <  2n - 1  <  n^2 - n - 1  <  n^2 - n + 1      (n : ℤ, 4 ≤ n)
```

From it both `explicit_family_pos` and `explicit_family_ne` are one-line corollaries. This is
preferred over six standalone disequality lemmas (which would be six copies of the same
transitivity argument) and over a `Finset.card = 4` statement (which hides the ordering that
later arguments actually use). The bound `4` is sharp: at `n = 3` the entries `2n-1` and
`n^2-n-1` are both `5`.

Everything is stated over `ℤ` with the hypothesis `4 ≤ n`. No `ℕ` version and no
`EqualTwoSquaresSolution` structure has been introduced yet: nothing needs them yet, and the
mission's own rule 7 says not to add an abstraction before two later theorems need it.

## Local files

- Scratch work: `examples/two-squares/Identity.lean`, `examples/two-squares/Family.lean`
  (both added to `lakefile.lean` as `lean_lib «TwoSquares»` roots; not a default target).
- Axiom check: `tmp/axiom_check_two_squares.lean` → `tmp/twosq_axioms.log`.
- Probe used for Mathlib discovery: `tmp/twosq_probe.lean` → `tmp/twosq_probe.log`.
- Definitions / theorem mirrors / submission sources: none (`Definitions/`, `Theorems/`,
  `Solutions/` are untouched).
- Mission scripts: `missions/two-squares/platform/build_proposal.py`
  (`--check` / `--fields` / `--sync` / `--status`), `platform/proposal.json`,
  `platform/description.md`, `platform/statements/All.lean` (+ `split_items.py` →
  `statements/items/*.lean`), `platform/readbacks/*.md`, `platform/proposal-receipt.json`.
  `platform/dropped/`.
- Submissions: `platform/submit_solutions.py` (`--check` / `--submit` / `--poll`),
  `platform/solutions/Sol_EqualTwoSquares_<name>.lean` (13 files, one root-level
  `theorem solution` each) + `<name>-explanation.md`, `platform/solutions/check_all.py`
  (wraps all 13 in separate namespaces, compiles once, prints `#print axioms` for each),
  `platform/solutions/AllSolutions.lean` (generated), `platform/submissions-receipt.json`.

## Theorems proved locally

All of the following are **proved**: `lake build TwoSquares` green and `#print axioms` reports at
most `[propext, Classical.choice, Quot.sound]` for each.

`TwoSquares` namespace, `examples/two-squares/Identity.lean`:

| theorem | statement |
|---|---|
| `sum_two_squares_mul` | `(p^2+q^2)(r^2+s^2) = (pr+qs)^2 + (ps-qr)^2` over any `CommRing` |
| `sum_two_squares_mul'` | `(p^2+q^2)(r^2+s^2) = (pr-qs)^2 + (ps+qr)^2` over any `CommRing` |
| `four_param_identity_ring` | `(pr+qs)^2+(ps-qr)^2 = (pr-qs)^2+(ps+qr)^2` over any `CommRing` |
| `four_param_identity` | same over `ℤ` (the shape asked for in Objective 1) |
| `four_param_gives_solution` | the `let a := …` reading that produces a solution |

`examples/two-squares/Family.lean`:

| theorem | statement |
|---|---|
| `explicit_family_identity (n : ℤ)` | `1^2 + (n^2-n+1)^2 = (2n-1)^2 + (n^2-n-1)^2` (all `n`) |
| `explicit_family_chain {n} (4 ≤ n)` | `1 < 2n-1 ∧ 2n-1 < n^2-n-1 ∧ n^2-n-1 < n^2-n+1` |
| `explicit_family_pos {n} (4 ≤ n)` | all four entries `> 0` |
| `explicit_family_ne {n} (4 ≤ n)` | all six pairwise disequalities |
| `explicit_family_solution {n} (4 ≤ n)` | identity ∧ positivity ∧ distinctness bundled |
| `familyQuad` | def: the quadruple `(1, n^2-n+1, 2n-1, n^2-n-1)` |
| `familyQuad_injective` | the parametrisation is injective on all of `ℤ` |
| `family_patterns_infinite` | `(Set.range familyQuad).Infinite` |
| `family_scaling_trivial` | `familyQuad n = k • familyQuad m → n = m` |
| `family_primitive (n : ℤ)` | gcd of the four entries is `1` |

Not proved, not claimed: nothing so far depends on anything outside the above. No numerical
evidence has been used and no external result has been assumed.

## Validation and submissions

Exact commands (all run 2026-09-26, from `D:\users\self_projects\prove2me_workspace`):

```bash
export PATH="/usr/bin:/bin:/c/Windows/System32:/c/Windows:$PATH"
lake env lean examples/two-squares/Identity.lean   # exit 0, 46 s combined run
lake env lean examples/two-squares/Family.lean     # exit 0
lake build TwoSquares                              # exit 0, 31 s, 910 jobs
lake env lean tmp/axiom_check_two_squares.lean     # exit 0
```

Axiom output (`tmp/twosq_axioms.log`): all five `Identity.lean` theorems report
`[propext, Quot.sound]`; the `Family.lean` theorems additionally use `Classical.choice`
(from `nlinarith`/`linarith`/`omega` certificates and `Set.infinite_range_of_injective`).
Nothing else. No `sorry`, no `axiom`.

### Platform submissions (2026-09-26 19:5x–20:2x)

```bash
py=C:/Users/anche/.workbuddy/binaries/python/versions/3.13.12/python.exe
cd missions/two-squares/platform
"$py" submit_solutions.py --check                            # signature + no-sorry + explanation
"$py" submit_solutions.py --submit --allow-pre-approval      # POST /verify, one per theorem
"$py" submit_solutions.py --poll                             # GET /submissions/<id>
cd solutions && "$py" check_all.py                           # one compile for all 13 + #print axioms
```

All 13 came back `ACCEPTED`. Each solution is a single root-level `theorem solution` with
`import Mathlib` — **no namespace wrapper** (a wrapped one is rejected with
`Unknown identifier 'solution'`). `check_all.py` reproduces the proof text verbatim inside
per-file namespaces, so a green run means every submitted file also compiles standalone.

Axiom output: every one of the 13 reports at most `[propext, Classical.choice, Quot.sound]`
(`Classical.choice` comes from the `omega`/`nlinarith` certificates and
`Set.infinite_range_of_injective`). No `sorry`, no extra axioms.

Two Lean traps hit while writing these, both worth remembering:

- **`rw [hXeq]` rewrites inside `Int.gcd X U`.** With `hXeq : X = r * ↑(Int.gcd X U)`, rewriting
  in a goal that also contains `Int.gcd X U` corrupts the gcd into `Int.gcd (r*g) U`. Fix: bind
  `let g : ℤ := (Int.gcd X U : ℤ)` and rewrite with `X = r * g`, so the gcd is an opaque local
  constant.
- **`Int.gcd` has no commutation lemma in this pin.** `exists_gcd_one` supplies `gcd r s = 1`
  while Euclid's lemma for the step `s ∣ r*Y ⟹ s ∣ Y` wants `gcd s r = 1`; derive the
  divisibility from Bézout (`Int.gcd_eq_gcd_ab`) instead, which uses only the given orientation.

Limitations worth recording:

- The proofs are **self-contained per item**: the platform compiles each submission alone, so
  `complete_parametrization` re-proves parity alignment, the half-sum substitution and the
  factorisation inline rather than importing them from the graph. The DAG on the platform is
  therefore not a dependency graph of the *proof text*, only of the statements.
- The mission says nothing about uniqueness of the parameters `p,q,r,s` for a given solution,
  and nothing has been proved about that.

## Draft items on the platform (all statements elaborate; `:= by sorry` one per file)

Namespace `EqualTwoSquares`. "Local proof" = already machine-checked in
`examples/two-squares/`, awaiting a `theorem_id` to be submitted against.

| local id | theorem | objective | local proof |
|---|---|---|---|
All rows below are **proved and `ACCEPTED`** on the platform (2026-09-26 20:2x). "Source" is the
local file that first established the proof, where one exists; `ESQ.PROD`, `ESQ.PAR`, `ESQ.HALF`,
`ESQ.FACT` and `ESQ.GOAL` were proved directly in the submission files.

| local id | theorem | objective | source |
|---|---|---|---|
| `ESQ.GOAL` | `complete_parametrization` | 6 | submission file (inline PAR + HALF + FACT) |
| `ESQ.BF` | `two_squares_mul` | 1 | `Identity.lean` |
| `ESQ.PARAM` | `four_param_identity` | 1 | `Identity.lean` |
| `ESQ.FAM` | `explicit_family_identity` | 2 | `Family.lean` |
| `ESQ.CHAIN` | `explicit_family_chain` | 2 | `Family.lean` |
| `ESQ.SOL` | `explicit_family_solution` | 2 | `Family.lean` |
| `ESQ.INJ` | `familyQuad_injective` | 3 | `Family.lean` |
| `ESQ.INF` | `family_patterns_infinite` | 3 | `Family.lean` |
| `ESQ.SCALE` | `family_scaling_trivial` | 3 | `Family.lean` |
| `ESQ.PROD` | `sum_sq_eq_iff_product` | 4 | submission file (`nlinarith` both ways) |
| `ESQ.PAR` | `parity_alignment` | 4 | submission file (mod 4, 16-case split) |
| `ESQ.HALF` | `sum_sq_eq_halves` | 4 | submission file (witnesses `X=a-k`, `Y=k`, `U=b-l`, `V=-l`) |
| `ESQ.FACT` | `four_factor_param` | 5 | submission file (gcd + Bézout) |

Note the platform statements differ slightly from the local ones: `familyQuad_injective` and
`family_patterns_infinite` inline the quadruple `(1, n^2-n+1, 2n-1, n^2-n-1)` instead of using the
local `def familyQuad`, because the platform has no definition node here; and `two_squares_mul`
bundles the two Brahmagupta–Fibonacci forms into one conjunction item.

`EqualTwoSquares.family_primitive` was drafted and audited but **not submitted**: the read-back
noted that with first entry `1` the statement reduces to `1 = 1` independently of `n`, i.e. it is
vacuous. See `platform/dropped/`.

## Next action

Everything in the mission's six objectives is done and accepted. What remains is bookkeeping and
whatever 宇轩 wants next:

1. **Wait for moderator approval** — `python build_proposal.py --status` until `mission_id` is
   non-null; then the 13 theorems become a live public mission instead of a proposal.
2. Optional extensions, none of them required by the mission text:
   - `ℕ`-entry variants and the `EqualTwoSquaresSolution` structure — still not introduced,
     because nothing yet needs them (mission rule 7).
   - A Gaussian-integer reformulation via `ℤ[i]` (`Zsqrtd.norm_mul`): explicitly secondary in
     the mission text; the elementary development does not need it.
   - Uniqueness of the parameters `p,q,r,s`: not asked for, not proved, and false as stated
     without normalisation.

Blockers: none. Pending platform IDs: none (all 13 `theorem_id`s resolved; see
`platform/proposal-receipt.json`).

## Communication

Mathematical work, code, and documentation: English. User-facing reports: Chinese.
