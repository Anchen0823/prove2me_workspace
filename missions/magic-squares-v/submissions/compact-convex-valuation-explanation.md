# Compact-convex indicator relation

For finitely many compact convex subsets of `ℝⁿ`, a pointwise rational linear
relation among their indicator functions forces the total coefficient of the
nonempty sets to vanish.

The proof proceeds by induction on the coordinate dimension. In dimension
zero, the space has a single point. For the induction step, fix the first
coordinate and restrict every set to that slice. Each slice is again compact
and convex, so the induction hypothesis gives a one-dimensional indicator
relation for the coordinate projections. Compact convex subsets of the real
line are empty sets or closed intervals, and the closed-interval endpoint
argument shows that this final relation preserves the total coefficient.

The valuation and coordinate-slicing strategy is inspired by Rolf Schneider,
[*Combinatorial identities for polyhedral cones*](https://home.mathematik.uni-freiburg.de/rschnei/Comb.Ident.rev.pdf),
Theorem 2.3 and equations (19)-(22), manuscript pages 6-8. This submission
proves only the indicator relation stated above. It does not claim a
formalization of the paper's complete Euler or local-face theory.

The standalone solution is generated deterministically from the six proved
local modules by `assemble_compact_convex_valuation.py`.
