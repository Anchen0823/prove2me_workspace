# Workspace layout

## Ownership

| Location | Responsibility |
| --- | --- |
| `missions/index.json`, `missions/README.md` | Registry and navigation for every mission, proposal, and maintenance workstream |
| `missions/<slug>/status.md` | Current target, dated platform evidence, blockers, next action; registry may point to an existing checkpoint or draft instead |
| `missions/<slug>/scripts/` | Mission-specific generation, validation, and submission scripts |
| `missions/<slug>/research/` | Source research and exploration records for new work |
| `missions/<slug>/verification/` | Submission IDs, verdicts, and verification evidence for new work |
| `examples/<area>/` | Lean development modules, sometimes shared by several missions |
| `Definitions/`, `Theorems/`, `Solutions/` | Stable platform module layout; theorem mirrors may contain `sorry` and are not proof acceptance evidence |
| `scripts/` | Shared API client, Lean extractors, workspace navigation and validation |
| `referpaper/` | Existing shared magic-square literature; mission-specific literature may live in its mission |
| `references/`, `SKILL.md`, `agent_docs/` | Platform API and agent workflow documentation |
| `docs/history/` | Archived workspace-wide chronology |
| `tmp/`, `.lake/` | Ignored transient experiments and build cache |

## Working on a mission

1. Run `python scripts/workspace.py list` or open `missions/README.md`.
2. Run `python scripts/workspace.py show <slug>` for the handoff, shared scratch
   location and available scripts. Read the handoff before running scripts.
3. Run commands from the repository root. Submission/create/seed scripts can write
   to the platform; navigation and `check` do not execute these scripts.
4. Put new scripts with the mission. Resolve the root from the script location
   (Python `Path(__file__).resolve().parents[3]`), not from the caller's directory.
5. Keep platform Lean modules at their stable paths. Shared scratch modules such
   as Spencer and Rosser are real Lake dependencies; do not move them casually.
6. Record outcomes in the mission handoff, with evidence under `verification/`.

## Adding a mission

Create `missions/<slug>/status.md` from the template, add one entry to
`missions/index.json` and one row to `missions/README.md`, and run
`python scripts/workspace.py check`. Use an existing family/scratch directory
when the mathematical infrastructure is shared. Create optional subdirectories
only when they have content. Do not copy shared platform definitions per mission.

## September 2026 migration

Mission scripts moved out of the shared scripts directory. Exact old-to-new paths
and original file hashes are in [script-migration.json](script-migration.json).
Use the new paths in external scheduled commands. Repository documentation and
script-to-script calls were updated; old paths in historical API evidence or
agent memory remain historical. Existing mission evidence and proof modules were
preserved. The former root dashboard is archived in `docs/history/`.
