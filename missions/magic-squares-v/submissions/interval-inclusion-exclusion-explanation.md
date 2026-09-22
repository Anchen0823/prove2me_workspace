# Finite-set interval inclusion-exclusion

For each `C ⊆ B`, the alternating sum over `S ⊆ D \ C` is one exactly when
`D ⊆ C`, and zero otherwise.  This rewrites the interval sum as a double
sum over `C ⊆ B` and `S ⊆ D` with `C` disjoint from `S`.

Swap the two finite sums.  For fixed `S`, the allowed `C` are exactly the
subsets of `B \ S`; applying the hypothesis identifies their `g`-sum with
`f (B \ S)`.  The remaining sign is `(-1) ^ |S|`, giving the formula.

The Lean solution proves this directly from `Finset.sum_powerset_neg_one_pow_card`
and elementary powerset/disjointness identities.  It is an independent finite
inclusion-exclusion argument, rather than a quoted external theorem.
