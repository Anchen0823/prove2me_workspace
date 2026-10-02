# Constructive support elimination for the sparse LP child

Target: `KKBinPacking.GeometricGrouping.exists_sparse_near_optimal_lp`,
https://prove2.me/theorems/a3149f0a-8819-48eb-a74d-26789cfba321

Status: mathematical blueprint and locally located Mathlib APIs only. No Lean
implementation of this child has been completed or submitted in this contribution.

First prove the following stronger sparsification result for any feasible vector:

```lean
theorem lp_sparsify
    (I : Multiset ℝ) (x : Multiset ℝ →₀ ℝ)
    (hx : IsLPFeasible I x) :
    ∃ y : Multiset ℝ →₀ ℝ,
      IsLPFeasible I y ∧ lpCost y ≤ lpCost x ∧
      y.support ⊆ x.support ∧ y.support.card ≤ numSizes I
```

Use the old support `S = x.support` as an index type, and the distinct item types
`T = I.toFinset` as row indices. Configuration `c` gives the vector whose `t`
coordinate is `(c.count t : ℝ)`. If `S.card > T.card`, these columns are linearly
dependent. Keep the indexed family rather than taking a finite-set image of the
columns: repeated columns must remain distinct indices.

Choose a nonzero kernel direction `d` and orient its sign so that its coefficient
sum is nonnegative. Some coefficient is positive: otherwise all coefficients
would be nonpositive and their nonnegative sum would force them all to vanish.
This step does not need a separate proof that the direction has both signs.

On the finite nonempty set where `d c > 0`, take the minimum ratio `x c / d c`.
It is positive because all entries on the support of a nonnegative vector are
positive. Subtract this ratio times `d` from `x`, extending by zero outside `S`.
The resulting vector is nonnegative, has exactly the same type coverage, has
non-increasing objective, and loses at least the index attaining the minimum
ratio. Its support remains inside the old support. Strong induction on support
cardinality finishes, or one can minimize support cardinality among feasible
vectors with non-increasing cost and contradict minimality.

This is a finite-support argument; it does not require enumerating all possible
configurations or proving that the global real LP infimum is attained. Obtain an
arbitrary solution within positive tolerance of the infimum from feasible-set
nonemptiness and the infimum property, then sparsify it without increasing cost.

Mathlib APIs located by GPT-6 Astra during read-only follow-up:

- `LinearIndependent.fintype_card_le_finrank`
- `Module.finrank_pi`
- `Fintype.not_linearIndependent_iff`
- `Finset.exists_min_image`
- `Finset.sum_eq_zero_iff_of_nonpos`
- `Finsupp.onFinset`, `Finsupp.support_onFinset_subset`
- `Finsupp.sum_of_support_subset`
- `Finset.card_lt_card`
- `exists_lt_of_csInf_lt`

Normalize all new-vector sums back onto `S` with
`Finsupp.sum_of_support_subset`; this avoids repeated changes of summation sets
in the coverage and objective calculations. The existing direct volume proof
already contains a definitions-only construction of a feasible singleton
packing, including the empty instance.
