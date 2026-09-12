# Explicit Chebyshev input audit

The remaining input is `abs(psi(y)-y) <= y/(40*log y)` for `y >= 10^8`.
Tao's proof of Lemma 4.3 explicitly invokes the corresponding estimate
from Schoenfeld Theorem 7. See
https://arxiv.org/html/1201.6656v4 (Section 4, proof of Lemma 4.3).
The original Schoenfeld PDF has not yet been independently retrieved;
the AMS endpoint returned HTTP 403. Cite this distinction honestly.

A fresh Prove2Me Schoenfeld search returned four results, none the needed
two-sided error bound. The quadratic mass target remains Open in the
matching environment. The response is research/schoenfeld-before-mass.json.

## External Lean project

Inspected public sources from AlexKontorovich/PrimeNumberTheoremAnd:

- `IEANTN/RosserSchoenfeld/RosserSchoenfeldPrime.lean`: `theorem_12`
  is `by sorry` (saved research/pnt-RSPrime.lean, line 1015).
- `IEANTN/TMEEMT.lean`: `RS_prime.theorem_a` wraps that theorem.
  Its blueprint checkmark does not establish an axiom-free proof.
- `Dusart1999.theorem_a` has a real reduction proof, but its
  `psi_theta_err` calls `Dusart.corollary_4_5`, which is `by sorry`
  in research/pnt-Dusart.lean. It also starts only at exp(22), so it
  would not cover the required 10^8 threshold without additional work.

These observations rule out the inspected routes as ready-made complete
proofs. They do not assert that every possible route in that project is
unproved. No external Lean source has been imported into the submission.

## Prepared contribution

The local placeholder `TaoFivePrimes.schoenfeld_psi_error_large` is NOT
published and NOT proved. The exact-target mass solution imports it as
the sole open dependency. `scripts/prepare_mass_sketch.ps1` assembles
the proof from checked helpers. Consult verification/mass-sketch-local*
for the full-file validation result. Do not submit the solution until
the source node is published and the import resolves on the server.

Publication update: source theorem 3fa7d8d1-e2ce-4057-894d-f39a2f0a4a8d is now published and Open. The mass sketch was submitted as 22e9d559-4993-4086-b1e9-bc4fecf541fe, currently PENDING. Earlier unpublished-placeholder notes above describe the preparation phase.

Catalog follow-up: both pages of the same-environment q=Chebyshev search
were inspected (140 results; research/chebyshev-catalog-current.json and
research/chebyshev-catalog-page2.json). MediumPNT is Proved but asserts
an existential positive constant in a Big-O estimate at infinity; it
supplies neither the 10^8 threshold nor the numerical error constant.
Vino.psi_le only gives N*log(N), also insufficient. No ready-made explicit
two-sided estimate was found in this search. The original AMS PDF remains
blocked by its web challenge; the indexed mirror failed transport. These
fetch failures do not constitute a mathematical disproof or a mission
blocker, and Tao's explicit source citation remains available.
