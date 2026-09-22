# Face/support order isomorphism for the real semi-magic cone

For `n ≥ 1`, the theorem identifies every face of the nonnegative real semi-magic cone with either the empty board or a matching-covered board. The order is inclusion on both sides. A cell belongs to the board exactly when some matrix in that face has a nonzero value there.

The proof first establishes that faces of a nonnegative subspace section are coordinate-zero faces. It then uses Mathlib's Birkhoff-von Neumann decomposition to show that positive supports of doubly stochastic matrices are exactly the matching-covered boards, and normalization transfers this to nonzero points of the cone. The empty board is realized by the zero matrix.

The related Birkhoff **polytope** face-lattice statement appears in [Beniamini and Nisan, arXiv:2001.07642v2, §3.2.2, Theorem 3.11](https://arxiv.org/pdf/2001.07642v2), where it is attributed to Billera and Sarangarajan. This submission proves a corresponding **cone** statement with an explicit support-witness property; it does not claim that the paper states the Lean theorem verbatim.

The public definition is in `Definitions/Def_MagicSquaresRealCone.lean`. The solution is generated from the eight proved local modules by `assemble_real_cone_face_support.py`. The definition and solution both compile with pinned Lean 4.33.1.
