# Prove2Me workspace dashboard

Navigation refreshed: 2026-09-20 (Asia/Shanghai). Platform state was not refreshed
as part of this local reorganization. Each mission handoff owns its dated status.

## Start here

- [All missions and workstreams](missions/README.md) — includes Magic Squares I–V,
  node maintenance, and the number-theory textbook proposal.
- [Workspace layout and contribution rules](docs/workspace-layout.md)
- [Earlier dashboard and full historical work log](docs/history/status-before-2026-09-20.md)
- [Platform workflow](SKILL.md)

## Work areas

| Area | Handoffs |
| --- | --- |
| Magic-square counting | [I](missions/magic-squares/status.md), [II](missions/semi-magic/status.md), [III](missions/normal3/status.md), [IV](missions/magic-squares-iv/status.md), [V](missions/magic-squares-v/status.md) |
| Magic-square maintenance | [Node reattachment](missions/magic-squares-reattach/status.md) |
| Analytic number theory | [Five primes](missions/five-primes/status.md), [Weak Goldbach](missions/weak-goldbach/status.md) |
| Euler gamma | [Session checkpoint](missions/euler-gamma/SESSION-CHECKPOINT.md) |
| Probability | [Bunkbed](missions/bunkbed/status.md) |
| Proposed work | [Number theory textbook](missions/nt-textbook-proposal/DRAFT.md) |

## Shared environment

Read `lean-toolchain` and `lake-manifest.json` for the pinned environment.
Keep `.lake/` for dependency and build reuse. Platform-facing module paths remain
`Definitions/`, `Theorems/`, and `Solutions/`; local helper targets are declared
in `lakefile.lean`. A different platform toolchain needs a separate checkout.

Update the relevant mission handoff after work. Keep detailed chronology there;
this page stays a short navigation dashboard.
