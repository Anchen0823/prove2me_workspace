# Mission: Weak Goldbach Conjecture (target: `WeakGoldbach.verified_two_primes_4e14_to_4e18`)

Last updated: 2026-09-15 (Asia/Shanghai)

## Objective and platform state

- Mission URL / ID: `570a7f0d-fb48-4f7f-bf81-ed919bd7a241` — "Weak Goldbach Conjecture".
- Mission root theorem: `WeakGoldbach.three_primes`, `bd7591ca-487c-46f4-83ff-9374082d13b0` (Open).
- Active target: `WeakGoldbach.verified_two_primes_4e14_to_4e18`,
  `24c6e94b-2b96-4f10-b16d-486fa48068eb`. Platform status after this session:
  **Open, now an internal node with exactly one Open leaf** (was a bare leaf).
- Open frontier of the active target (2026-09-15):
  `WeakGoldbach.verified_range_sieve_coverage`,
  `73e8ddac-1271-41d0-b9d1-1add55e1e714` (Open, `closability` 0).
- Position in the mission tree:

  ```
  three_primes
  └ goldbach_odd_variant
    └ strong_goldbach_conjecture
      └ goldbach
        └ even_goldbach_to_4e18
          └ verified_two_primes_to_4e18
            ├ verified_two_primes_4e14_to_4e18   ← active target
            │ └ verified_range_sieve_coverage    ← new child (Open)
            └ Richstein2001.even_goldbach_up_to_4e14
              └ Richstein2001.segmented_sieve_coverage
  ```

- Lean toolchain: `leanprover/lean4:v4.33.1`.
- Mathlib revision: `0df444a360eaa60ab8c11dca51a86af692955474` (default env).

## Source and strategy

- Exact source: T. Oliveira e Silva, S. Herzog, S. Pardi, *Empirical verification of the
  even Goldbach conjecture and computation of prime gaps up to $4\cdot10^{18}$*,
  Math. Comp. **83** (2014), no. 288, 2033–2060,
  <https://doi.org/10.1090/S0025-5718-2013-02787-1>. The target is the segment of the
  verified binary range strictly above Richstein's $4\cdot10^{14}$.
- Mission discussion (`GET /missions/:id/comments`, jjosh, 2026-09-11) classifies this
  node as one of the "irreducible cores": a genuine verified-computation claim, not a
  provable statement with current tooling. A direct Lean proof would have to decide the
  Goldbach property for $\approx 2\cdot10^{18}$ even numbers.
- Established platform pattern for exactly this kind of node: `Richstein2001.even_goldbach_up_to_4e14`
  was reduced (submission `ebe8dd2c-f282-4249-883c-20ad9bafa738`, SKETCH_ACCEPTED) to the
  single finite sieve-coverage obligation `Richstein2001.segmented_sieve_coverage`, using the
  published `Definitions.Def_GoldbachSieve` interface. That accepted sketch was read back with
  `GET /submissions/ebe8dd2c-.../solution` and used as the design template here.
- Key source parameters for the extension segment:
  - largest smaller prime in a minimal Goldbach partition of an even $n\le 4\cdot10^{18}$ is
    $9781$, attained at $n = 3\,325\,581\,707\,333\,960\,528$ (OEIS A025019 / A025018;
    tabulated at <https://sweet.ua.pt/tos/goldbach.html>). Richstein's corresponding value on
    $\le 4\cdot10^{14}$ is $5569$.
  - sieve cutoff: $2\cdot10^{9} = \sqrt{4\cdot10^{18}}$, forced by the square-root completeness
    of the survivor test (Richstein's is $2\cdot10^{7} = \sqrt{4\cdot10^{14}}$).
- Decomposition chosen: one child, the finite block-indexed sieve-coverage obligation
  `WeakGoldbach.verified_range_sieve_coverage`, mirroring the Richstein formalization but with
  the extension-segment parameters and the block grid anchored at $4\cdot10^{14}$.

## Local files

- Definition mirror: `Definitions/Def_GoldbachSieve.lean` (byte-for-byte the published
  `GoldbachSieve` definition, created locally so the workspace can compile the reduction).
- Child mirror: `Theorems/Thm_WeakGoldbach_verified_range_sieve_coverage.lean` (`by sorry`).
- Target mirror: `Theorems/Thm_WeakGoldbach_verified_two_primes_4e14_to_4e18.lean` (`by sorry`).
- Submission source: `Solutions/Sol_WeakGoldbach_verified_two_primes_4e14_to_4e18.lean`
  (sorry-free; inlines `GoldbachSieve.survivor_prime` and `GoldbachSieve.pairSums_sound`).
- Scratch / checks: `examples/weak-goldbach/` (`scratch1..3.lean`, `checktype.lean`).
- Payloads, explanations, evidence: this directory (`missions/weak-goldbach/`).
- API helper: `scripts/p2m_api.py`; child payload builder: `scripts/submit_weak_goldbach_child.py`.

## Validation and submissions

Local, all with `lake build` / `lake env lean` on the pinned toolchain:

- `lake build Definitions.Def_GoldbachSieve Theorems.Thm_WeakGoldbach_verified_range_sieve_coverage`
  — success (only the expected `sorry` warning for the mirror).
- `lake build Solutions.Sol_WeakGoldbach_verified_two_primes_4e14_to_4e18` — success, no
  diagnostics; `grep -n "sorry\|admit"` on the submission returns nothing.
- `lake env lean examples/weak-goldbach/checktype.lean` — prints

  ```
  WeakGoldbach.verified_two_primes_4e14_to_4e18 : ∀ (m : ℕ),
    4 * 10 ^ 14 < m → m ≤ 4 * 10 ^ 18 → Even m → ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ m = p + q
  solution : ∀ (m : ℕ), 4 * 10 ^ 14 < m → m ≤ 4 * 10 ^ 18 → Even m → ∃ p q,
    Nat.Prime p ∧ Nat.Prime q ∧ m = p + q
  ```

  i.e. the submission's type is syntactically identical to the target's.

Platform:

- Child published as a problem: job `42ea4b0b-49b7-4153-ba8e-b4fb3a142cad` → **PUBLISHED**,
  `WeakGoldbach.verified_range_sieve_coverage`, theorem id
  `73e8ddac-1271-41d0-b9d1-1add55e1e714`
  (evidence: `child-publish-response.json`, `child-publish-job.json`).
- Reduction submitted for the target: submission
  `7020cdba-e182-45ee-9d64-dd2512d4562c`, `proof_type=prove` → **SKETCH_ACCEPTED**,
  `error_message` empty (evidence: `reduction-submit-response.json`, `reduction-verdict.json`).
- Decomposition confirmed by a fresh read: the target now has children
  `GoldbachSieve` (definition) and `WeakGoldbach.verified_range_sieve_coverage` (Open).
  Target open-leaves now returns exactly the new child
  (evidence: `target-decompositions.json`, `target-open-leaves.json`).
- Problem ratings cast for the target, the new child, and `Richstein2001.segmented_sieve_coverage`
  (`POST /rate` accepted 3) — payload in `ratings.json`.

Explicit non-claim: the target is **not** proved. `SKETCH_ACCEPTED` records a reduction, not a
proof; `WeakGoldbach.verified_range_sieve_coverage` remains Open, and the whole Weak Goldbach
mission is unaffected. No arithmetic content of the computation was verified on the platform.

## Next action

Attack `WeakGoldbach.verified_range_sieve_coverage` (`73e8ddac-1271-41d0-b9d1-1add55e1e714`).
It is a finite, purely combinatorial obligation in the `GoldbachSieve` interface over
$4\cdot10^{12}+1$ blocks; any progress needs either compact certificate data or a further
reduction that splits the block range into independently checkable pieces. Do not resubmit the
target: submission `7020cdba-e182-45ee-9d64-dd2512d4562c` is already accepted and the
decomposition edge exists. `Richstein2001.segmented_sieve_coverage` is the sibling obligation in
the same interface and can reuse the same steps.

## Communication

Mathematical work, code, and documentation: English. User-facing reports: Chinese.
