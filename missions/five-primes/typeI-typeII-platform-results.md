# Type I and Type II platform results

Verified on 2026-09-13. Both connected estimates are now **Proved** on Prove2Me.

| Theorem | Platform theorem ID | Evidence |
| --- | --- | --- |
| TaoFivePrimes.theorem51_typeI_bound | d0fdae67-dec9-4bf7-9f8e-7772e9446b85 | Complete proof a4144d51-5149-4860-b501-1c52d5cf290d, ACCEPTED |
| TaoFivePrimes.theorem51_scale_bound_signed | b111b484-f725-4569-8504-3d222a36c577 | Complete proof 01825288-444e-47ce-977d-b0f445697fa4, ACCEPTED |
| TaoFivePrimes.theorem51_typeII_of_scale_bound | b46d7b94-7c1d-4d9d-980f-18230c005f4c | Complete proof f5179f27-fc47-4065-97d8-6db29f368927, ACCEPTED |
| TaoFivePrimes.theorem51_typeII_bound | 605a083b-e6e1-4471-b532-c6f34ea1a76a | Reduction 13a21c90-5dd8-416e-82bb-7dc312825516; both children Proved; parent Proved |

The integration proof connects the actual double tsum to the scale integral,
handles exact odd reindexing and support, integrates the coupled radical bound,
and establishes the target constants 0.1, 0.39, 0.55 and 0.78.

## Validation

- Lean: leanprover/lean4:v4.33.1.
- Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474.
- `scripts/check_theorem51_progress.ps1`: 53 source modules, 39.18 seconds,
  exit 0, no sorryAx. The script regenerates its combined check source.
- Exact submitted integration solution: 37.70 seconds, exit 0, no sorryAx.
  SHA256: 7AE4E08CF2F53778ABCD68E94A864BB025A86DA07E2D3EC6DDE00B681B8BC1B6.
- Current server snapshots and immutable submission verdicts are saved under
  `verification/`; the connected decomposition is under `research/`.
- Theorems/ files are platform statement references and intentionally contain
  placeholders. The complete Solutions/ files contain no placeholders.
- The upstream finite spectral identity retains its Apache-2.0 attribution;
  see `third-party/Apache-2.0.txt` and the source header.

## Remaining original dependency

Theorem 5.1 and the original large-q target are not fully proved yet.
`TaoFivePrimes.theorem51_vaughan_split` remains Open
(197dea21-9471-497e-ba7a-3372b3e6eab7). The generic arithmetic identity and
support lemmas exist locally, but their concrete sum/norm assembly is not yet
proved. Do not infer full mission completion from the two proved estimates.

The Git milestone records the requested Type I/II platform completion. It does
not declare the broader dependency-resolution objective complete.
