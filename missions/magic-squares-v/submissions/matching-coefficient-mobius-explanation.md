# Matching coefficient as a Möbius number

For positive `n`, consider the finite poset containing the empty board and every matching-covered board, ordered by inclusion. The public coefficient `matchingEulerCoefficient n B` is the Boolean alternating transform of the indicator that a board contains a permutation support.

The proof first establishes its principal-ideal sum: over all subboards of a board `B`, the coefficient sums to the indicator that `B` contains a permutation. Coefficients outside the matching-covered support vanish, so this identity transfers to the matching-board subtype. Restoring weight `1` at the empty board and negating all nonempty coefficients gives precisely the bottom Möbius prefix identity. Uniqueness of finite Möbius weights then identifies the restored weights with `IncidenceAlgebra.mu`; the stated minus sign follows because a matching-covered board is nonempty.

The matching-covered support poset is related to the Birkhoff-polytope face lattice in Beniamini and Nisan, arXiv:2001.07642v2, Section 3.2.2, Theorem 3.11. The submitted coefficient identity is proved directly by finite Möbius inversion and is not claimed to be the paper's verbatim statement.
