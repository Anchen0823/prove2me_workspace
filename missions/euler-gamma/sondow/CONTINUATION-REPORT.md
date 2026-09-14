# Analytic formalization progress

The three original open children were revisited. This pass completes three analytic prerequisites and connects them to the two original analytic targets. It does not establish the infinite-occurrence conjecture or the irrationality milestone.

Final server verdicts: all three direct proofs are **ACCEPTED**. Both reductions are **SKETCH_ACCEPTED**, with no verification error. Their dependency branches were read back from the server.

## Complete proofs accepted by the server

| Result | Theorem ID | Submission ID |
|---|---|---|
| Positive integral decay: `0 < I n < (1/16)^n` | `27c6fe99-da87-4ba6-870b-10ab9e038045` | `c6b9dd94-7d0f-494e-9178-4d8c00243e2c` |
| Geometric-cutoff remainder tends to zero | `fd0d6179-45fd-43aa-819e-5e803fd80c1d` | `d3c21834-06ba-42c7-b715-d410b51d3eb7` |
| Finite harmonic/logarithmic correction tends to zero | `c6bf4441-d3be-46f0-a6b1-4343826caf49` | `56821675-abd4-4f13-9bfa-e99755151104` |

Each proof compiles under Lean v4.33.1 / Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, with `autoImplicit=false`. Their axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`; no open platform theorem is imported.

The integral estimate uses an elementary logarithmic majorant and strict integration on the open square. In particular, it does not depend on the still-open gamma integral identity. The remainder proof verifies both applications of dominated convergence, including measurability, domination and integrability. The finite-shift proof uses the harmonic recurrence and continuity of log at 1.

## Connections to the original targets

`scaled_integral_bounds` is reduced to the completed integral estimate and the existing `TaoFivePrimes.rosser_schoenfeld_psi_bound` node. The reduction proves `d (2*n) < 8^n` from that bound and Mathlib's identification of `log(lcmUpto)` with Chebyshev psi. The prime-estimate node is still Open; it was reused instead of duplicated. Its returned graph contained no Sondow/EulerMascheroni node.

`integral_identity` is reduced to the completed two zero-limit lemmas and the exact finite cutoff evaluation. Mathlib supplies the Euler-constant limit; uniqueness of limits completes the inference. The remaining finite evaluation is theorem `d27e4fda-75c8-48f4-bc64-5050678b070c`. It encapsulates the actual integration and combinatorial identity, not an irrationality hypothesis. See `FINITE-EVALUATION-NOTES.md` for its explicit proof route.

The two reduction submission IDs are `fb0b9d61-d8cb-48ac-85c1-706e7168f85c` and `d8eba62a-98e7-4a07-bbcf-9f42f90a8cb8`, respectively. Their local checks are conditional on imported child statements and are not unconditional proofs of the parents.

## Remaining frontier

1. The finite cutoff evaluation: a known source-derived identity still requiring its integration and combinatorial formalization.
2. The reused Rosser--Schoenfeld estimate: a known theorem whose platform branch still has formalization gaps.
3. The Sondow fractional-part infinite-occurrence conjecture: an unresolved mathematical assertion, unchanged in this pass.

Thus the two original analytic targets are not yet unconditionally proved. The third original child has no known proof in the cited source to translate. No numerical calculation is presented as evidence of an infinite theorem.

## Evidence

Final local source hashes, return codes and axiom output are in `continuation/*-local.json` and `*-local.log`. Publication and verification responses are saved in the same directory. The exact coefficient audit compares two independently assembled finite expressions for all 64 pairs `1 <= n,N <= 8`; this is an indexing/sign check, not a Lean proof of the finite identity.
