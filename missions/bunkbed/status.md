# Bunkbed Mission Archive

Status: **Completed**. Platform status was verified on 2026-09-12 (Asia/Shanghai).

All paths below are relative to the workspace root unless linked explicitly.

## Verified outcome

- Mission: **The Bunkbed Conjecture Is False**.
- Mission ID: `f428c039-066f-47c4-b246-7f531b8ad8f5`.
- Root: `BunkbedFalse.bunkbed_conjecture_false`.
- Root theorem ID: `6619f63b-95ee-4233-8741-8f51852d2990`.
- Root status: **`Proved`**; `/open-leaves` returned an empty list and `total: 0`.
- Final target: `BunkbedFalse.sub_probability_grouping` (`a6bfde9e-efba-4ee3-a87f-0edb760aa61f`).
- Final submission: `cbc9cab1-d2fd-4ea0-ae33-93402c2c8b82`, **`ACCEPTED`** at `2026-09-12T17:30:22.768007+08:00`.
- Automatic resolution also marked `sub_probability_transfer` and `explicit_counterexample` as `Proved`.

## Deliverables and evidence

- [Accepted grouping source](../../Solutions/Sol_BunkbedFalse_sub_probability_grouping.lean).
- [English proof explanation](explanation.md).
- [Server verdict](verification/GroupingVerdict.json).
- [Empty root frontier](verification/GroupingRootFrontier.json).
- [Resolved theorem chain](verification/GroupingResolvedChain.json).
- [Full historical handoff](handoff-history.md), preserved verbatim. It contains superseded blockers and pre-archive paths; use this page for current paths and status.
- [Archive manifest](archive-manifest.json), recording every original path, destination, and original SHA-256, plus hashes of the formal Lean modules kept in place.

The accepted grouping source SHA-256 is `17A3390AED50533FDC16DFC2031791205C5AD553386F1E1F7DAA7C4D94E3F1D3`. Formal source files were not edited during archiving.

## Earlier accepted contributions

| Target | Submission | Verdict at submission |
| --- | --- | --- |
| `BunkbedFalse.explicit_counterexample` | `484ffebe-3c12-4abb-95e6-563dfe1da4ab` | `SKETCH_ACCEPTED` |
| `BunkbedFalse.sub_probability_transfer` | `f0a19b81-ad19-4ca5-8273-6c05603bddde` | `SKETCH_ACCEPTED` |
| `BunkbedFalse.sub_gadget_copies_disjoint` | `db4c52cd-b9fe-4f6b-8f57-e0375ec40149` | `ACCEPTED` |

These sources remain in `Solutions/`, and platform definition and theorem mirrors remain in `Definitions/` and `Theorems/`.

## Reproduce validation

Run from the workspace root:

```powershell
.\missions\bunkbed\scripts\check_grouping.ps1
```

To also rebuild and validate the relocated successful scratch modules:

```powershell
.\missions\bunkbed\scripts\check_grouping.ps1 -CheckScratch
```

The standalone submission previously compiled locally in 31.52 seconds. Its exact target-type comparison also passed. Local theorem mirrors contain `sorry` placeholders, so `#print axioms solution` reports `sorryAx` locally; the platform accepted the submitted proof and its proved dependencies. The submitted source contains no `sorry`, custom axiom, or `native_decide`.

## Scratch archive and performance lessons

Scratch sources are under `examples/bunkbed/`; their [README](../../examples/bunkbed/README.md) distinguishes checked modules from failed historical attempts. Logs and server responses are under `missions/bunkbed/verification/`. The old standalone `GroupingCore.olean` was retained under `.lake/bunkbed-archive/` as a historical cache artifact; fresh relocated modules build under `.lake/build/lib/lean/examples/bunkbed/`.

The successful proof separates abstract finite-sum algebra from concrete graph instantiation. In the final connection, `Fintype.piFinset` and `gadgetE` are locally irreducible, preventing elaboration and linting from expanding enormous concrete configuration spaces. Keep simp lists narrow and use explicit finite-sum identities. Do not rerun failed monolithic drafts as the validation entry point.

## Environment and remaining work

Lean `leanprover/lean4:v4.33.1`; Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

Archive validation on 2026-09-12 passed with `missions/bunkbed/scripts/check_grouping.ps1 -CheckScratch`: both relocated helper modules, the final connection, the standalone submission, and the exact target-type check all compiled. The complete five-invocation run took 186.09 seconds; this is not the timing of a single submission compile. Only the pre-existing unused-simp-argument warnings were emitted. See [the archive validation log](verification/ArchiveValidation.log).

All 25 formal Lean source files retained their original hashes. All 26 moved files passed hash checks immediately after relocation; four scratch imports were then updated and recorded in the archive manifest. The new index and archive documentation passed local-link checks. Credentials and cache artifacts remain gitignored.

No remaining work or polling is required for this mission frontier. No Git commit or GitHub publication was performed as part of the archive operation. Selecting the next mission is a separate task.
