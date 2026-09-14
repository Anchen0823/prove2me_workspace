# Exact Rosser finite-prefix certificates

The original finite-middle obligation remains `1000 < n < 10^8`. These certificates prove prefixes of that interval; they do not close the obligation or the large-argument analytic estimate.

## Verified results

- `Solutions/SondowRosserMiddleTree1000000.lean`: `1000 < n` and `n <= 1000000` imply `Chebyshev.psi n < 1.03883 * n`. Full local validation exited **0** in **1864.6460892 seconds** (31.08 minutes). SHA256: `02B998F400BA544BE5842F3AABB6BC03A45ED5E531A2D4DE17A3C51830630C93`. The final axiom report contains exactly `propext`, `Classical.choice`, and `Quot.sound`. This closes the stated prefix only, not the original finite-middle target through `10^8`.

- `Solutions/SondowRosserMiddle10000.lean`: `1000 < n` and `n <= 10000` imply `Chebyshev.psi n < 1.03883 * n`; 60 blocks, 338725 source bytes.
- `Solutions/SondowRosserMiddle100000.lean`: the same statement through `100000`; 120 blocks, 3473469 source bytes. Local Lean validation exited 0 in 40.3083547 seconds. SHA256: `6290A46C6EE8B9EFC1E3737AB2006CA84C3E27629A3B3B6FFAFCFCC02FDE85DF`.

Both axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx` or `native_decide` is used. Neither prefix has been submitted as a proof of the full finite-middle target.

The implementation reuses the existing `examples/five-primes/RosserLcmBlocks.lean` and `RosserLcmCertificate.lean`. The generator supplies exact LCM values and interval endpoints. Lean checks the LCM block equalities, powers-of-two bounds, rational numerical inequalities, and coverage of the full stated prefix. Python output alone is not a proof.

## Scalability experiment

`generate_rosser_middle.py` now supports an experimental upper limit of one million and streams LCM values, retaining only certificate endpoints. The one-million certificate must receive an exit-zero Lean verdict and clean axiom report before being treated as verified. The limit is deliberately bounded: this experiment does not establish that the method scales to one hundred million.

The generated decimal one-million certificate has 181 blocks and 35367730 source bytes. Its largest block contains 37294 integers. Its Lean check failed with repeated maximum-recursion-depth errors starting at line 489, and was stopped after 251.19 seconds to avoid processing more doomed branches. The saved result has exit code -1. This file is not a proved result. It was subsequently moved out of the library to `continuation/failed-recursion-rosser-middle-1000000.lean`, preserving its contents and hash; the old filename in the historical result JSON identifies its original validation location.

The generator has subsequently been optimized to update the LCM only at prime powers, cache numeral strings, and emit hexadecimal numerals by default (`--numeral-format decimal` remains available). `Solutions/SondowRosserMiddleHex10000.lean` independently passed Lean with only the three standard axioms listed above, and its 60 interval endpoints and power exponents match the previous decimal certificate exactly. This optimization changes untrusted data generation and representation, not the mathematical proof interface.

`Solutions/SondowBalancedLcm.lean` adds a structurally recursive, balanced interval-LCM evaluator and proves its equality with the original `Finset.Ioc` LCM. Its certificate interface `lcmUpto_eq_of_balanced_block` builds with only the three standard axioms. The generator's `--balanced` option uses this theorem to avoid linear-depth interval evaluation. The regenerated `Solutions/SondowRosserMiddleBalanced1000000.lean` has 181 blocks and 29389539 source bytes; generation took 2.4945297 seconds. Its Lean validation was stopped without a verdict after 1168.58 seconds, once the separate-certificate structure below was validated on a smaller interval. It is not a completed prefix.

The integral-identity target is already complete on Prove2Me; see `INTEGRAL-IDENTITY-COMPLETE.md`. The full two-target completion objective remains active.

## Verification-cost diagnostics

The complete recursive-evaluator check (former session 91624) was stopped as described above. A separate exact check of its largest block (951282 to 988576, 699800 source bytes) was run with ordinary `decide` and stopped without a verdict after 166.20 seconds, to avoid redundant resource pressure. Exit code -1 is a stopped diagnostic, not evidence that the equality is false.

The local Lean 4.33.1 implementation in `Lean/Elab/Tactic/Decide.lean` distinguishes ordinary elaborator reduction from `decide +kernel`, which constructs a cached auxiliary lemma checked by the kernel. The generator exposes `--kernel` for this mode. This does not select `native_decide`. A largest-block diagnostic using this mode was stopped without a verdict after 231.65 seconds (former session 7123). No speedup was established. Its output and result are saved as `continuation/balanced-largest-block-kernel.log` and `...-result.json`.

## Separate interval certificates

`Solutions/SondowLcmTreeCertificate.lean` proves two unconditional composition lemmas: `intervalLcm_eq_of_split` combines two independently certified interval LCM values, and `lcmUpto_eq_of_certified_block` extends a certified prefix. Both have clean standard-axiom reports.

`--certificate-tree --kernel` generates leaf interval proofs of at most 128 integers, then verifies numerical LCM merges separately. This avoids asking the kernel to repeatedly evaluate a large recursive LCM expression in one proof. The resulting `Solutions/SondowRosserMiddleTree10000.lean` passed in 37.7716672 seconds with only the three standard axioms. Its 60 covering intervals match the previous certificates.

The one-million version has 181 covering intervals and 95749945 source bytes. Session **58484 completed successfully**, with log and result at `continuation/rosser-middle-tree-1000000.log` and `...-result.json`. See the verified result above; do not restart that completed check.

## Sol review and compact applications

At the user's request, a bounded Sol subagent reviewed only the generator and composition-lemma file, without inheriting the conversation history. It found no correctness issue and recommended inferring repeated numerical arguments. It implemented new compact wrappers while preserving the old explicit interfaces. The parent reviewed the changes, added `compact` to the generated metadata, and performed all Lean validation.

Both compact wrappers build with only `propext`, `Classical.choice`, and `Quot.sound`. The generated `Solutions/SondowRosserMiddleTree10000Compact.lean` passed in 41.1362406 seconds, SHA256 `2D3811DD9B24DBA8332A2B98DC17131AA9D8398CB858DFBCD463FBE6857CA5A3`, with the same clean axiom report.

`--certificate-tree --compact --kernel` reduces the million-prefix source from 95749945 to 35709059 bytes (62.71%). All 181 covering intervals and exponents remain identical. `Solutions/SondowRosserMiddleTree1000000Compact.lean` has been generated but NOT checked. The original noncompact million check succeeded in session 58484. No verification-speed improvement has been established: the small checks ran under different concurrent workloads, and source-size reduction alone is not a timing result.

For the next large check, retain an `.olean` output using Lean's `-o` option so a successful expensive validation can be reused by imports. Enable `-Dtrace.profiler=true -Dtrace.profiler.threshold=2000` to record slow elaboration steps. These options were checked against the local Lean source (`Lean/Util/Trace.lean`); they have not been applied retroactively to session 58484. Do not stop or duplicate that live check merely to change logging.

The completed million check did not write an `.olean`; preserve its source and exit-zero evidence, and do not claim a reusable binary artifact exists. The subsequent `decide_cbv` largest-block diagnostic failed with `simp`'s maximum-step limit after 201.9012278 seconds (session 2212, exit 1). Its `sorryAx` output belongs to a failed diagnostic and is not part of the proved million theorem. It provides no verified speedup. All these check sessions are now terminal.
