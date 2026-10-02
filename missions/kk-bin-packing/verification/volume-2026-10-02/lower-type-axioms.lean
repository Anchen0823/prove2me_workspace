import Solutions.Sol_KKBinPacking_GeometricGrouping_size_le_lin
open KKBinPacking.Shared KKBinPacking.GeometricGrouping
example (I : Multiset ℝ) (hI : IsInstance I) : SIZE I ≤ LIN I := solution I hI
#print axioms solution
