import Solutions.Sol_KKBinPacking_GeometricGrouping_alg2_iterations_le

set_option autoImplicit false
open KKBinPacking.Shared KKBinPacking.GeometricGrouping

example (k : ℕ) (hk : 2 ≤ k) (g : ℝ) (hg0 : 0 < g) (hg1 : g ≤ 1)
    (I : Multiset ℝ) (hI : IsInstance I) (tr : Alg2Trace k g I) (ht : 1 ≤ tr.t) :
    (tr.t : ℝ) ≤ Real.log (SIZE (tr.inst 0)) / Real.log k + 1 := by exact solution k hk g hg0 hg1 I hI tr ht

#print axioms solution
