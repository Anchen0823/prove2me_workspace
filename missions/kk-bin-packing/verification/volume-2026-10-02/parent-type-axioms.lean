import Solutions.Sol_KKBinPacking_GeometricGrouping_size_le_lin_le_opt_le_lin_add
open KKBinPacking.Shared KKBinPacking.GeometricGrouping
example (I : Multiset ℝ) (hI : IsInstance I) : SIZE I ≤ LIN I ∧ LIN I ≤ (OPT I : ℝ) ∧ (OPT I : ℝ) ≤ LIN I + ((numSizes I : ℝ) + 1) / 2 := solution I hI
#print axioms solution
#print axioms KKRoundingUpper.upper_from_sparse_approx_and_rounding
