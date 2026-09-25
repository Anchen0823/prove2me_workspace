# Rosser verification timeout repair

Scope: repair the 300-second verification timeout shown in the user's screenshot.
This is a performance repair of the existing reduction, not a complete proof of
the two outstanding analytic/finite inputs.

## Evidence

- Original submission: `603f8cd6-63dc-4609-86ab-78ad326fcf66`.
- Live original verdict: `ERROR`, `Verification timed out after 300s`.
- Previous local check: 227.327 seconds.
- Repaired exact submission file: local Lean check passed in 77.237 seconds,
  using Lean 4.33.1, the pinned Mathlib revision, and `autoImplicit=false`.
- Submitted SHA-256:
  `DEC726B231C3E54E5A2EDF572361317E2261E89D2C63BACD0AFEF6AC3D329D51`.
- Replacement submission: `11751692-de02-4b67-8b2f-44fe1593d392`.
- Final server verdict: `SKETCH_ACCEPTED`, with an empty error message.
- Live target remains `Open`; the accepted decomposition has exactly the two
  original Open theorem inputs listed below.
- Server verdict is saved in `verification/rosser-timeout-fixed-verdict.json`.

## Changes

The 87-way disjunctive cover proved with a single `omega` search is replaced
by an explicit balanced case tree of depth at most seven. Each leaf checks
its small interval with `omega` and reuses the existing exact endpoint proof.
The unused standalone LCM-at-1000 demonstration and unused ArcSplit import
are removed. All 87 interval certificates, including the delicate endpoint
113, are retained. No new imported assumptions, axioms, or native evaluation
are introduced.

`missions/five-primes/scripts/prepare_rosser_sketch.ps1` invokes
`missions/five-primes/scripts/optimize_rosser_timeout.py`, so regenerating the submission preserves
the performance repair. `missions/five-primes/scripts/submit_rosser_timeout_fix.ps1` checks the
original timeout, current target, exact verified file hash, and duplicate
submission markers before sending the repair.

A separate scratch experiment with narrower Mathlib imports also passed
(56.696 seconds with profiling). It is not the submitted file; the measured
77.237-second file is the one sent to the server.

## Mathematical boundary

The small range `1 <= n <= 1000` is proved in the submission itself.
The remaining imported inputs are `rosser_psi_finite_middle` and
`schoenfeld_psi_error_large`. An accepted sketch therefore does not mean
the full Rosser theorem is proved.
