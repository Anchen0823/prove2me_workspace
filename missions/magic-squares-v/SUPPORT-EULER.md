# Support constants and the finite Euler problem

Date: 2026-09-22.

Later continuation: [FINITE-BOUNDARY-REDUCTION.md](FINITE-BOUNDARY-REDUCTION.md)
gives a stronger finite hypothesis that propagates to full reciprocity and
determines the sign from the leading coefficient. That finite hypothesis remains
unproved; the identities in this file are unconditional supporting results.

The live root now has one open leaf, `MagicSquares.ehrhart_macdonald_birkhoff_pos`
(`985f7b0a-962f-4039-804c-794f2ce86533`). The platform already contains the
positive-count translation and polynomial-reflection bridges, and the specialized
orders one through four are proved. See the saved [live audit](research/2026-09-22-reciprocity/audit.md).

## New unconditional identities

Let `F_B(X) = closedPoly n B` count matrices whose support is contained in a
board B. On boards without a perfect matching this polynomial is zero and only
represents **positive** line sums. Let `E_B(X) = qB n B (X-1)` count exact support,
again at positive line sums, and let `s(B)=E_B(0)`.

Partitioning matrices by their support and using polynomial uniqueness gives

$$F_B(X)=\sum_{C\subseteq B}E_C(X).$$

Since the closed-support construction proves that `F_B(0)` is one precisely
when B contains a perfect matching, this yields the identity on every board

$$\sum_{C\subseteq B}s(C)=\mathbf1_{\{B\text{ contains a perfect matching}\}}.$$

An independent inclusion-exclusion proof gives the inverse identity for the
whole polynomials:

$$E_B(X)=\sum_{S\subseteq B}(-1)^{|S|}F_{B\setminus S}(X).$$

In particular,

$$s(B)=\sum_{S\subseteq B}(-1)^{|S|}
\mathbf1_{\{B\setminus S\text{ contains a perfect matching}\}}.$$

These statements use the existing closed-support polynomial proof, finite
counting, inclusion-exclusion, and polynomial uniqueness. They do not assume
Ehrhart reciprocity. The new source is
`examples/magic-squares/spencer/SupportConstants.lean`, with independent counting
interfaces in `SupportPartition.lean` and `SupportExactIE.lean`.

For a board that is not `IsSupport`, the alternating sum is zero, by the
existing vanishing of its exact-support polynomial. Thus this part of the
experimental pattern has an arbitrary-order proof.

`SupportCoverage.lean` also identifies realizable supports for positive n:
a board is an `IsSupport` exactly when it is nonempty and every edge belongs to
a perfect matching contained in the board. The forward proof repeatedly
subtracts a permutation matrix until the chosen edge belongs to the matching;
the converse sums all contained permutation matrices. Consequently a board
with an edge lying in no contained perfect matching has alternating sum zero.
This connects the experiment's matching-covered predicate to the Lean support
predicate without assuming any geometric reciprocity theorem.

## Connection to the first unknown negative value

Assume n is positive and write U for the full board. Adding one to every entry is a bijection from
semi-magic squares at line sum t to exact-full-support squares at line sum
t+n. Therefore polynomial uniqueness gives `E_U(X+n)=P(X)`.
Evaluating this at X=-n identifies the first negative value outside the
already-proved vanishing range:

$$P(-n)=s(U)=\sum_{S\subseteq U}(-1)^{|S|}
\mathbf1_{\{U\setminus S\text{ contains a perfect matching}\}}.$$

This identifies the value without assuming reciprocity. Evaluating the sum as
`(-1)^(n-1)` for arbitrary n remains the finite Euler problem; the formula is
not a claim that this sign has been proved.
The identity is formalized in `FirstNegativeValue.lean`, including its
polynomial shift and evaluation at `-n`.

## Precise remaining finite identity

The former `ReciprocityAtNegOne n` assertion is now equivalently the claim
that the displayed alternating sum equals `(-1)^rankB B` for every realizable
nonempty support. This equivalence is formalized; neither side is assumed proved.
For a matching-covered bipartite graph, the expected rank is

$$|B|-2n+c(B),$$

where c(B) is its number of connected components. The graph-rank identification
is used in the experiment, not imported as an unproved Lean assertion.

The script `scripts/check_support_euler.py` computes the Boolean subset Möbius
transform on **every** board for orders 1 through 4. There are respectively
1, 3, 49, and 7443 nonempty matching-covered boards; every one has the predicted
sign. All other boards have zero coefficient. Results are saved in
`research/2026-09-22-reciprocity/support-euler-experiment.json`.
This is a finite experiment, not a general proof or a kernel-checked certificate.

Proving this finite sign identity would resolve the support constant problem.
It would **not by itself** establish all negative evaluations: a further argument
propagating reciprocity through the support recurrences, or a geometric
reciprocity theorem, is still required. No new platform reduction is claimed
from this work.

## Validation

The new support identities, local all-ones translation, and first negative-value
formula compile with pinned Lean 4.33.1 (8727-job dependency build). Eighteen public results were checked with
`#print axioms`; each depends only on `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx`. Source hashes and build targets are
recorded in `verification/support-constants-record.json`. These are local
results; no new platform proof or sketch was submitted.
