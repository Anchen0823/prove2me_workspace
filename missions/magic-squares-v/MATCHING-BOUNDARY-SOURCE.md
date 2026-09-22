# The matching-boundary Euler identity: a finite face-lattice route

Update: the matching-core operations and a general weighted Weisner cancellation
are now formalized. See [INTERVAL-EULER.md](INTERVAL-EULER.md) for the refined
route: the remaining sufficient hypothesis is the zero coefficient sum on each
nondegenerate matching-covered interval. The geometric Euler justification
below remains informal; the finite-sum propagation no longer is.

This note gives a mathematical derivation of the finite identity used by
`FiniteBoundaryEuler`.  It is **not** a Lean formalization and does not close
the reciprocity mission.  Its purpose is to isolate one finite combinatorial
theorem whose proof would suffice for the already-checked conditional Lean
reduction.

The external lattice facts used below are standard consequences of the face
lattice of a convex polytope.  For a source, see Richard Stanley,
[*Enumerative Combinatorics*, vol. 1, 2nd ed.](https://math.mit.edu/~rstan/ec/ec1.pdf),
Proposition 3.8.9 on p. 309 and Corollary 3.9.3 (Weisner's theorem) on p. 313.
The specialization below is our own derivation; it is not claimed to be a
verbatim statement of either result.

## Finite objects and the proposed identity

Fix `n >= 1`.  A board is a subset of the `n^2` cells.  Write `HasPerm(B)` when
`B` contains the support of a permutation matrix, and put

\[
 a(B)=\sum_{E\subseteq B}(-1)^{|B|-|E|}\,[\operatorname{HasPerm}(E)].
\]

Equivalently, this is the `sB_eq_alternating_hasPerm` Boolean Möbius
coefficient, with the complementary subset reindexed.  A board is
*matching-covered* when it is nonempty and every one of its cells occurs in a
permutation support contained in it.  These are precisely the positive exact
supports; in the Lean development the finite replacement of `IsSupport` is
`MagicSquaresSpencer.isSupport_iff_perm_coverage`.

For matching-covered `D <= B` and a permutation support `phi <= B`, the finite
boundary statement is

\[
 \sum_{\substack{D\le C\le B\\C\cup\phi=B}} a(C)
 =
 \begin{cases}a(B),&\phi\le D,\\0,&\phi\not\le D.\end{cases} \tag{MB}
\]

Since `C <= B` and `phi <= B`, the condition `C union phi = B` is equivalent
to `B \ phi <= C`; it is exactly the `fiberCandidates` condition in
`SupportSplit.lean`.

## The face-poset dictionary

Let `P_n` be the Birkhoff polytope.  The nonempty faces of `P_n` are indexed
by matching-covered boards, ordered by support inclusion.  Under this
identification, the join is union of supports.  To obtain a lattice one adjoins
the empty face as a formal bottom element; this formal bottom is not a positive
exact support and is not assigned a matching-covered board coefficient.

For any board `X`, let `core(X)` be the union of all permutation supports
contained in `X`.  If `HasPerm(X)`, this is a matching-covered board and is the
support of the smallest face containing exactly those vertices permitted by
`X`.  A matching-covered board `C` lies in `X` exactly when its face is a
nonempty face of `F_core(X)`.  Consequently, the Euler relation for a nonempty
polytope face gives

\[
 \sum_{\substack{C\subseteq X\\C\text{ matching-covered}}}
 (-1)^{\dim F_C}
 = [\operatorname{HasPerm}(X)]. \tag{1}
\]

Here the left side is the alternating sum over all nonempty faces of a
polytope: it is `1` when the face exists, and the sum is empty otherwise.

Define `h(C)=(-1)^dim(F_C)` for matching-covered `C`, and `h(C)=0` otherwise.
Equation (1) says precisely that the Boolean zeta transform of `h` is
`HasPerm`.  The definition of `a` says the same for `a`.  Boolean Möbius
inversion therefore yields

\[
 a(C)=h(C)=(-1)^{\dim F_C}\quad\text{for matching-covered }C,
 \qquad a(C)=0\quad\text{otherwise}. \tag{2}
\]

The zero statement for non-covered boards is already available in the Lean
development.  The remaining mathematical input behind (2) is the standard
face-poset Euler relation, not Ehrhart reciprocity.

## Deriving (MB) from Weisner

First suppose `phi <= D`.  Every `C` in the sum has `phi <= C`, hence
`C union phi = C`.  The boundary condition forces `C=B`, so the left side is
`a(B)`.

Now suppose `phi` is not contained in `D`, and set

\[
 A=D\vee\phi=D\cup\phi.
\]

Then `D < A <= B`.  Work in the finite lattice interval `[D,B]` of the face
lattice.  Its dual form of Weisner's theorem says that for any element
strictly above its bottom,

\[
 \sum_{\substack{D\le C\le B\\C\vee A=B}}\mu(D,C)=0. \tag{3}
\]

This is Corollary 3.9.3 applied to the order-dual interval.  The strictness
`D<A` is essential: it supplies the hypothesis that the distinguished element
is not the bottom of this interval.  Because `D<=C`,

\[
 C\vee A=C\vee(D\vee\phi)=C\vee\phi.
\]

Thus the indexing condition in (3) is exactly the indexing condition in (MB).

The face lattice is Eulerian.  Hence for `D<=C` its Möbius value is

\[
 \mu(D,C)=(-1)^{\dim F_C-\dim F_D}.
\]

Using (2), this rearranges to

\[
 a(C)=(-1)^{\dim F_D}\mu(D,C).
\]

Multiplying (3) by the constant `(-1)^dim(F_D)` proves that the left side of
(MB) is zero when `phi` is not contained in `D`.  Together with the first case,
this proves (MB).

## Boundaries of the claim

This argument depends on proving, in the chosen formal setting, the
face/support dictionary, the join-as-union fact, the face-lattice Eulerian
property, and the dual Weisner specialization.  None of those steps is
currently supplied as a Lean theorem in this route. The elementary `phi <= D`
branch is now proved in `examples/magic-squares/spencer/MatchingBoundaryEasyCase.lean`;
the outstanding part is the zero sum when `phi` is not contained in `D`.
The local script
`check_permutation_boundary_euler.py` supplies only finite evidence (`n <= 3`
exhaustively and a deterministic `n = 4` sample); it is not a proof of (MB).

If (MB) is formalized, `FiniteBoundaryBalance.lean` proves
`FiniteBoundaryEuler -> BoundaryBalance`, and the subsequent files prove the
conditional reciprocity and root reductions.  Until then, the platform root
and reciprocity targets remain open.
