# Beniamini--Nisan source audit

Audited copy: arXiv:2001.07642v2, SHA-256 `C71B5CE343B5D868D53D2A419DFB76A97A9AF26F346B374D3F12CB171B7790DF`.

Section 3.2.2 states Theorem 3.11 (Billera--Sarangarajan): the Birkhoff face lattice is the inclusion lattice of matching-covered graphs plus the empty graph. Lemma 3.12 derives its bottom Mobius numbers from Euler--Poincare. Section 3.2.3 proves strict cyclomatic monotonicity (Lemma 3.13 and Corollary 3.13.1), a one-step ear deletion (Lemma 3.14), and hence `rk(G) = chi(G)+1` (Corollary 3.14.1). Section 3.2.4 then proves Theorem 1:

`BPM_n = sum_{G in MC_n} (-1)^chi(G) monomial(G)`.

This agrees in shape with the public `matchingEulerCoefficient`: both are Boolean-Mobius coefficients of the perfect-matching-existence indicator, zero off realized matching supports, and alternating on supports. Their conventions need checking: the paper adjoins an empty graph and fixes the vertices of `K_{n,n}`; for `n >= 1`, its nonempty matching-covered graphs have no isolated vertices. The Lean coefficient must retain its own empty-board and `n = 0` behavior.

This is source evidence, not a Lean proof: Lemma 3.12 still uses polytope Euler--Poincare, so it does not discharge the missing finite Euler/interval-cancellation bridge.
