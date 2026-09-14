# Completion objective

## Current execution constraint and priority

The user has now supplied the original 1975 PDF. The former source-access
blocker is resolved; do not request that PDF again. See the updated
`INFINITE-RANGE-STATUS.md` for its hash, visually verified statements, and the
three-row simplification of the psi-only table argument. Current work proceeds
on this route with scoped Sol/Terra/Luna subtasks authorized by the user.

The user requires each theorem to pass Prove2Me verification within 300 seconds and has selected the infinite-range leaf first. Suspend expansion of finite certificates. The million-prefix check took 1864.6460892 seconds locally, so it is not platform-ready. A locally compiled dependency does not by itself establish that an uploaded standalone proof meets the server limit. Prioritize `TaoFivePrimes.schoenfeld_psi_error_large` without changing its statement or adding unproved assumptions. Tao's Lemma 4.3 cites reference [44], Rosser and Schoenfeld (1975), Theorem 7; the 1976 Part II paper is not that cited source.

Completely prove the original `integral_identity` and `scaled_integral_bounds` targets. Completion means both exact original statements have status Proved on Prove2Me, backed by accepted proofs whose dependency frontier is empty. More reductions alone do not satisfy this objective.

## Current authoritative status: integral target complete

`integral_identity` is now **Proved**, with **zero open leaves**, confirmed by live readback. Its finite-cutoff dependency was accepted in direct submission `38bdc812-0ccc-4d5b-804b-5552822b8c18`. All integration, cutoff algebra, rectangle, reflection and logarithmic-form proofs are complete. No new graph nodes were added. See `INTEGRAL-IDENTITY-COMPLETE.md` and the saved verdict/readback JSON. Do not redo these proofs; earlier open-work notes below are historical.

The remaining task is **scaled_integral_bounds**, with the two prime-estimate leaves below. The full goal remains active. PNT+ revision `a5154676af9aa3095150ee410cdda80555aa0642` was audited: the apparently completed `RS_prime.theorem_a` wrapper calls `RS_prime.theorem_12`, still `by sorry` at RosserSchoenfeldPrime.lean line 1015. That wrapper cannot close this target. Exact upstream snapshots are saved in `continuation/upstream-*.lean`.

**Session 58484 is now terminal, exit 0:** the entire million-prefix certificate passed in 1864.6460892 seconds with only the standard three axioms. Do not restart this completed check. The CBV largest-block diagnostic (session 2212) is also terminal: it failed after 201.90 seconds with the simplifier step limit, so it is not a proof or an established optimization. No Lean job from these experiments remains live. A second bounded Sol source audit is complete: no directly usable elementary replacement was established. Costa Pereira 1989 remains unassessed because the actual PDF could not be accessed; an initial inference from a `10^11` search example was explicitly withdrawn. See `ELEMENTARY-LCM-SOURCE-CHECK.md`. This is not evidence that an elementary route is impossible, and no new Graph nodes were added.

## Historical frontier on goal entry

Current local progress on the finite-middle leaf: unconditional kernel-checked certificates cover **1001..1000000**. `Solutions/SondowRosserMiddleTree1000000.lean` (181 covering intervals, 95.75 MB) passed; its SHA256 is `02B998F400BA544BE5842F3AABB6BC03A45ED5E531A2D4DE17A3C51830630C93`. The log and exit-zero result JSON are `continuation/rosser-middle-tree-1000000.log` and `...-result.json`. The first recursive experiments are historical and unproved. See `ROSSER-FINITE-CERTIFICATES.md` for all modes and results. The compact million file is generated but not checked; only its 10000 regression file and wrappers are verified. No prefix was submitted as a solution of the full leaf, whose upper limit remains `10^8`. Further finite work needs a scalable certificate strategy and cached compilation; simply rerunning the proved million prefix does not advance the goal. Additional upstream error-bound wrappers were audited and found to depend on holes; see `UPSTREAM-ERROR-BOUND-AUDIT.md`.

- `integral_identity` (747d96a7-9576-41e1-801a-228e9d36c4cd): finite cutoff identity (d27e4fda-75c8-48f4-bc64-5050678b070c).
- `scaled_integral_bounds` (00b4cd42-5f36-4d22-ab0f-2a87c9194496): Schoenfeld large-argument error (3fa7d8d1-e2ce-4057-894d-f39a2f0a4a8d) and Rosser finite middle (d7089f63-d516-4c70-a5f5-f1ae1e917931).

The user's graph agrees with the live API. Existing accepted integral bounds, remainder limits, correction limits, and parent reductions remain reusable.

## Original execution route (item 1 now complete)

1. Finite cutoff identity: formalize the rational improper integral underlying the logarithmic moments, then the moment integral itself with justified integration order. Expand the finite geometric truncation, telescope its diagonal and off-diagonal sums, and prove the logarithmic-form combinatorial identification. Reuse `Nat.sum_range_choose_sq` and `Int.alternating_sum_range_choose_of_ne` instead of reproving their underlying identities.
2. Scaled bound: retain the existing Rosser interface while evaluating the remaining effective prime-estimate proof. Mathlib's current coarse Chebyshev bound has main constant log 4, too large to imply the required bound; substituting it does not close the target. A finite computation alone cannot prove the large-argument leaf. Any alternative must prove the original quantitative bound for all positive n, not weaken it to an eventual or slower decay statement.
3. Upload completed proofs only after local type checking and axiom checks; read back the exact two target statuses and their open leaves before declaring completion.

## Completed local continuation: logarithmic moments

`Solutions/SondowFiniteMoments.lean` now builds successfully with its three supporting modules. The rational improper integral, reciprocal-log Laplace representation, product-space absolute integrability, Fubini evaluation of the double moment, and diagonal/off-diagonal finite sums all have unconditional axiom reports (no sorryAx). See `MOMENT-FORMALIZATION-REPORT.md` for exact scope and file hashes. Resume from polynomial/geometric expansion and combinatorial coefficient identification, rather than redoing these integrations. These local modules have not yet been published to the server; the original targets are not complete.

## Completed local continuation: finite cutoff analysis and algebra

`Solutions/SondowCutoffAlgebra.lean` now proves the signed-form finite-cutoff identity, with all integral evaluations, finite expansions, integration exchanges, index shifts and coefficient extractions proved. Its conditional wrapper has the exact original finite-cutoff conclusion and the single explicit remaining hypothesis `signedLogForm n = L n`. The published L definition remains unchanged. Resume at Sondow Lemma 2 / Appendix Proposition 10; do not redo the integration or cutoff algebra. See `CUTOFF-FORMALIZATION-REPORT.md` and `continuation/cutoff-algebra-local.log`. This is local work, not a new server submission; both original target frontiers were refreshed and remain Open.

## Work policy

English Lean code and research artifacts, Chinese progress reports. Preserve the full objective across turns. The fractional-part conjecture is outside this completion objective. The user has requested use of lower-tier models such as Sol for subagents to reduce consumption. Sol task `/root/certificate_efficiency_review` completed a bounded review, then implemented compact wrappers and a generator flag in the two specified files; no conversation history was copied, and it started no Lean jobs. The parent reviewed and verified its changes: compact wrappers and the compact 10000 certificate pass with clean axioms. The compact million source is generated (35.71 MB vs 95.75 MB) but is NOT checked; the original full million check passed. Prefer narrowly scoped delegation over duplicating the full problem. Do not mark the goal complete while either analytic target still has open dependencies.
