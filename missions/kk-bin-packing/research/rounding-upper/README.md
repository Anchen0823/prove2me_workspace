# Lemma 2 upper bound: exact remaining core

Source: Karmarkar and Karp, FOCS 1982, p. 313, Lemma 2.
https://pagesperso.g-scop.grenoble-inp.fr/~newmana/OptApproxFall2016/Karmarker-Karp-BinPacking.pdf

`UpperReduction.lean` proves the upper bound from two explicit open core hypotheses and the already-proved `opt_le_two_size_add_one`. It imports definitions only and supplies no proof of either core hypothesis.

Suggested child 1, sparse near-optimal configuration LP:

```lean
theorem exists_sparse_near_optimal_lp
    (I : Multiset ℝ) (hI : IsInstance I) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : Multiset ℝ →₀ ℝ,
      IsLPFeasible I x ∧ lpCost x < LIN I + ε ∧
      x.support.card ≤ numSizes I
```

This is the support consequence of the paper's optimal-basic-solution argument, weakened to arbitrarily close optima to avoid demanding attainment unnecessarily. It still needs substantive finite LP geometry. The configuration set is finite because all types have positive size and each bin has capacity one. Merely invoking `IsBasicFeasible` is insufficient: its current definition has no bundled support bound.

Suggested child 2, general floor/delete certificate:

```lean
theorem lp_floor_rounding_certificate
    (I : Multiset ℝ) (hI : IsInstance I)
    (x : Multiset ℝ →₀ ℝ) (hx : IsLPFeasible I x) :
    let R := I - (principalConfigs x).join
    ∃ P : Multiset (Multiset ℝ),
      IsPacking (I - R) P ∧
      P.card ≤ principalCount x ∧
      SIZE R ≤ lpCost x - (principalCount x : ℝ) ∧
      (OPT R : ℝ) ≤ (x.support.card : ℝ)
```

This child is valid for every feasible solution and is independently reusable. Principal configurations can contain surplus items, so the bins `P` must be trimmed. For each type the residual count is truncated subtraction, bounded by the fractional slot supply. Summing weighted residual counts gives its volume bound. One copy of each fractional configuration covers the residual after trimming, yielding its support-cardinality bound.

The Lean reduction glues an optimal residual packing to P. The residual cost is bounded by both the support count and twice the residual volume plus one; their minimum is at most residual volume plus half the support count plus one half. The sparse near-optimal objective then gives the claimed exact bound by arbitrary positive tolerance.

Known boundaries: neither new child has been proved here; no platform theorem imports or `sorry` appear in the conditional proof. Formal proof of the certificate still needs multiset trimming, per-type floor accounting, and the conversion from integral configuration covers into exact packings.
