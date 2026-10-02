import Solutions.Sol_KKBinPacking_GeometricGrouping_lin_le_opt

set_option autoImplicit false
open KKBinPacking.Shared KKBinPacking.GeometricGrouping

example (I : Multiset ℝ) (hI : IsInstance I) : LIN I ≤ (OPT I : ℝ) := by exact solution I hI

#print axioms solution
