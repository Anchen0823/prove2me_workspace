# Complete proof of the matching-boundary criterion

Let a(C) be the matching Euler coefficient in the public definition. The proof
first establishes the interval identity

$$\sum_{D\subseteq C\subseteq B}a(C)
 =\sum_{S\subseteq D}(-1)^{|S|}[B\setminus S\text{ contains a perfect matching}].$$

For matching-covered boards D properly contained in B, we prove that this sum
vanishes. Let P_B be the polytope of nonnegative real matrices supported in B
whose row and column sums are all one. It is compact, since its equations are
closed and every entry lies between zero and one. Averaging the permutation
matrices supported on a matching-covered board gives a doubly stochastic
matrix positive exactly on that board. Choose such points x_D and x_B.

For sufficiently small epsilon > 0, the affine point
q = (1 + epsilon)x_D - epsilon x_B is positive on D, nonpositive off D, and
negative at some coordinate j in B minus D. It satisfies the affine equations
of P_B but lies outside its nonnegative orthant. For x in P_B put

$$d(x)=x_j-q_j>0,\qquad \pi(x)=\frac{x-q}{d(x)}.$$

Every coordinate face of P_B has a compact convex image under pi. Compactness
follows from continuity with a nonvanishing denominator. For convexity, a
convex combination of two normalized points is the normalization of a convex
combination of their preimages with weights reweighted by the positive
denominators.

For i in D let F_i be the coordinate face where x_i=0. The images pi(F_i) cover
pi(P_B): each ray from q meeting P_B has a last point by compactness. If this
point had no zero coordinate in D, it could be extended slightly while
remaining nonnegative and satisfying the affine equations, contradicting
maximality. Moreover pi is injective on the union of these faces. If two
boundary points satisfy x=q+t(y-q), a zero coordinate of x with q_i>0 forces
t>=1, while a zero coordinate of y forces t<=1. Thus t=1. Consequently pi
preserves every nonempty finite intersection of these coordinate faces.

We separately prove, by induction on the coordinate dimension, that any
pointwise-zero finite rational linear combination of compact-convex indicators
has total coefficient zero when empty sets have weight zero. The induction
uses coordinate slices and the elementary closed-interval endpoint identity.
This is inspired by the slicing strategy in Rolf Schneider,
[Combinatorial identities for polyhedral cones](https://home.mathematik.uni-freiburg.de/rschnei/Comb.Ident.rev.pdf),
Theorem 2.3. The perspective-shadow argument above is the specialization used
here; we do not assume the paper's local Euler identities.

Apply finite inclusion-exclusion to the cover of pi(P_B) by the pi(F_i), then
apply the compact-convex indicator relation. Images preserve nonemptiness, so

$$\sum_{S\subseteq D}(-1)^{|S|}
 [P_B\cap\{x_i=0\ (i\in S)\}\ne\varnothing]=0.$$

A coordinate face in this formula is nonempty exactly when B minus S contains
a perfect matching: one direction uses a supported permutation matrix, and
the other extracts a permutation from the positive support of a doubly
stochastic matrix. This proves the required interval cancellation.

Finally the finite weighted Weisner argument in MatchingIntervalReduction
converts these interval cancellations into the public matching-boundary
criterion, including its separate branch when the selected permutation is
already contained in the lower board. The standalone solution proves all
steps and imports only Mathlib and the two public definitions, with no open
theorem dependency. It does not assume a general face-lattice Euler theorem
or a dimension-sign formula.
