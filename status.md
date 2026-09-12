# Prove2Me Workspace Status

Last updated: 2026-09-12 (Asia/Shanghai)

## Current work

Active mission: **Every Odd Number Greater Than 1 is the Sum of at Most Five Primes**. See [the mission handoff](missions/five-primes/status.md).

Current phase: autonomous mission work is stopped at the user's requested submission boundary. The Rosser reduction was submitted as 603f8cd6-63dc-4609-86ab-78ad326fcf66; its last observed verdict was PENDING, and polling has stopped. Its finite-range child is published as d7089f63-d516-4c70-a5f5-f1ae1e917931 (Open). Earlier complementary correlation is Proved and the quadratic mass reduction is SKETCH_ACCEPTED. The mission remains Open; its latest verified frontier had 13 leaves. Resume mission work only on an explicit user request.

Write mathematical work, Lean code, and handoff documents in English. Report progress to the user in Chinese.

## Mission index

| Mission | Status | Handoff |
| --- | --- | --- |
| Every Odd Number Greater Than 1 is the Sum of at Most Five Primes | Open; 13 frontier leaves on 2026-09-12; complementary correlation Proved, quadratic prime mass Open | [Five-primes handoff](missions/five-primes/status.md) |
| The Bunkbed Conjecture Is False | Root `Proved`; zero open leaves, verified 2026-09-12 | [Bunkbed archive](missions/bunkbed/status.md) |

## Start the next mission

1. Obtain the mission URL or ID from the user and inspect its current root, milestones, open frontier, and prior attempts using the project skill.
2. Check the target's `mathlib_rev` against the environment below. Use a separate checkout for a different environment; do not mix theorem mirrors from different environments here.
3. Create `missions/<slug>/status.md` from [the status template](missions/_template/status.md), and use `examples/<slug>/` for scratch Lean files.
4. Keep platform modules at `Definitions/Def_*.lean`, `Theorems/Thm_*.lean`, and `Solutions/Sol_*.lean`. These paths mirror server imports and are shared across missions in the same environment.
5. Save mission-specific explanations and verification responses under `missions/<slug>/`. Update this page to point to the active mission.

## Shared environment

- Lean: `leanprover/lean4:v4.33.1`.
- Mathlib revision: `0df444a360eaa60ab8c11dca51a86af692955474`.
- Keep `.lake/` to reuse installed dependencies and build artifacts.
- Follow [SKILL.md](SKILL.md) and [the mission solver workflow](references/mission_solver.md).
- `credentials.json` remains at the root and is gitignored. Never print or commit its contents; send credentials only to `https://prove2.me/api/v1`.

Local organization does not modify platform submissions or theorem status. The five-primes implementation phase has submitted two accepted proof sketches and one accepted complete proof; details are in its mission handoff.
