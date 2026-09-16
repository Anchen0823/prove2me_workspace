# Project memory — prove2me_workspace

## Environment (Windows, this machine)

- Bash starts with a broken PATH: every Bash command must begin with
  `export PATH="/usr/bin:/bin:/c/Windows/System32:/c/Windows:$PATH";`.
- The PowerShell tool returned no captured output in this session — prefer Bash.
- Lean: `leanprover/lean4:v4.33.1` via `elan`; Mathlib
  `0df444a360eaa60ab8c11dca51a86af692955474`, already built under `.lake/`.
  Never delete `.lake/`.
- Ad-hoc checking: `lake env lean <file.lean>` (raw `lean.exe` needs
  Windows-style `LEAN_PATH` entries). Module checks: `lake build <Module.Name>`.
- `omega` can fail with "maximum recursion depth" on `Nat` goals mixing huge
  literals with `/`; split into explicit `Nat.div_mul_le_self` /
  `Nat.add_le_add_left` / `calc` steps, or raise `maxRecDepth`.
- **Finset binder notation**: `∑ k in s, f k` does NOT parse in this Mathlib
  revision — always write `∑ k ∈ s, f k` (works, and `#check` prints it that way).
- `Finset.eq_empty_iff_forall_not_mem` does not exist; use
  `Finset.not_nonempty_iff_eq_empty` (`¬ s.Nonempty ↔ s = ∅`).
- `lakefile.lean` sets `autoImplicit false` for the libs (`Definitions`,
  `Theorems`, `Solutions`), but `examples/` is **not** a `lean_lib`, so
  `lake env lean examples/...` runs with autoImplicit ON. Always move a proof
  into `Solutions/` and re-check before submitting.
- Any `def` using `Finset.filter` on a propositional predicate must sit inside
  `noncomputable section`, or Lean rejects the generated `Classical.propDecidable`.

## Prove2me conventions

- API helper: `scripts/p2m_api.py` (`token`, `get`, `raw`, `post`, `patch`,
  `verify`, `patch-explain`). Credentials live in `credentials.json`; never print
  or commit them.
- Pass JSON bodies as files (`python scripts/p2m_api.py post <path> <file>`);
  inline single-quoted JSON gets mangled by this shell.
- Do not issue two Edit calls to the same file in one message — parallel
  read-modify-write races lose one of them.
- A reduction imports children as `import Theorems.Thm_<name with '.' → '_'>`
  (e.g. `MagicSquares.center_of_order_three` →
  `Theorems.Thm_MagicSquares_center_of_order_three`), never the target itself, and
  must be `sorry`-free; the child must be published with `/submit-problem` first.
  Submissions are asynchronous: poll `/verify?submission_id=` to a terminal
  status (`ACCEPTED` / `SKETCH_ACCEPTED` / `FAILED`), and poll
  `/publish-jobs/<job_id>` for problems/definitions. `/submission/{id}` is a
  404 HTML page — the polling endpoint is `GET /verify?submission_id=`.
- **Publish order is a hard dependency.** A problem whose `preamble` imports
  `Definitions.Def_X` fails with `unknown import` if `Def_X` was submitted in the
  same command and is not yet `PUBLISHED`. Submit the definition, poll it to
  PUBLISHED, then submit the problems.
- Local mirrors of platform theorems for offline type-checking go in
  `Theorems/Thm_<slug>.lean` (built with `lake build Theorems.Thm_<slug>`).
- Preamble may hold imports and `set_option` only; own `def`s go through
  `/submit-definition` as `Definitions.Def_<name>`.
- **Self-containment gate before every submit.** Local `lake` resolves
  local-only modules that the server does not have. A `Solutions/*.lean` may only
  import things actually published on the platform — check the mission node list
  first. Concretely, `Definitions.Def_TaoFivePrimes_Theorem51VinogradovSharp`
  compiles locally but is **not** on the platform (only
  `TaoFivePrimes_Theorem51Sums` / `0638cceb` exists), so any submission using it
  fails server-side. Inline such helpers into the solution file instead.
- **Never trust node IDs recorded in `session-*.md` / `report-*.md`.** They drift
  and some were fabricated across summarizations. Re-read the live list:
  `python tmp/list_nodes.py [name-filter]` pages `/theorems?mission_id=...`
  (the helper already exists; otherwise quote the URL — see below).
- `python scripts/p2m_api.py raw '<path>?a=b&c=d'` — **the path must be
  single-quoted**, else bash eats `&` and the request 404s.
- Nodes published via `/submit-problem` without a `mission_id` land **outside**
  the mission DAG (their `/theorems/<id>/graph` shows `edges = []`). Pass
  `mission_id` when you want the node inside the graph.

## Reusable proof technique: beating a too-weak "count" hypothesis

When a hypothesis carries a covering count `⌊W/L⌋ + 1` that over-counts at the
very case you need (here `W = L`, giving 2 instead of 1), do **not** try to extract
the sharp count — a larger count is a *weaker* bound, so it cannot be sharpened by
rewriting. Instead split:

1. Bound the LHS by `#terms · A` using `#terms ≤ q` obtained from an interval
   **cardinality** (`Int.card_Ioc` on a width-`q` interval gives exactly `q`),
   which avoids any integer division / `⌊·/2⌋` bookkeeping.
2. Recover `q · A ≤ RHS` from a **degenerate instance** of the same hypothesis
   chosen so that every summand is exactly `A` and the count is exactly 1.

Choosing the degenerate phase so the sine vanishes *identically* is what makes
step 2 work with no analytic input and no coprimality hypothesis.

## Mission design pattern (learned from the Weak Goldbach mission)

For mission nodes that are genuine finite computational verifications
("verified-computation cores"), the platform's accepted pattern is to reduce
them to a **finite, block-indexed certificate obligation** in a published
interface (here `Definitions.Def_GoldbachSieve`: `survivors`, `pairSums`), with
the reduction itself inlining the generic soundness lemmas
(survivor ⇒ prime needs `hi ≤ cutoff^2`; `pairSums` ⇒ Goldbach representation).
Neighbours: `Richstein2001.segmented_sieve_coverage`,
`WeakGoldbach.verified_range_sieve_coverage` (`73e8ddac`).

Mission handoffs live in `missions/<slug>/status.md`; scratch Lean goes in
`examples/<slug>/`; platform evidence (payloads, verdicts, JSON reads) is stored
next to the handoff.
