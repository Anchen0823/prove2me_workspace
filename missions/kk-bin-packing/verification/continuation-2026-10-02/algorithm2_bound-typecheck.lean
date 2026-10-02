import Solutions.Sol_KKBinPacking_GeometricGrouping_algorithm2_bound

set_option autoImplicit false
open KKBinPacking.Shared KKBinPacking.GeometricGrouping

example (k : ℕ) (hk : 2 ≤ k) (g : ℝ) (hg0 : 0 < g) (hg1 : g ≤ 1 / 2)
    (I : Multiset ℝ) (hI : IsInstance I) (hS : 1 ≤ SIZE I)
    (P : Multiset (Multiset ℝ)) (hP : Alg2Run k g I P) :
    IsPacking I P ∧
      (Multiset.card P : ℝ) ≤
        max ((1 + 2 * g) * (OPT I : ℝ) + 1)
          ((OPT I : ℝ) + (1 + Real.log (SIZE I) / Real.log k) *
              (1 + 4 * (k : ℝ) + 2 * (k : ℝ) * Real.log (1 / g)) +
            2 + (2 / (1 - 1 / (k : ℝ))) * Real.log (1 / g)) := by exact solution k hk g hg0 hg1 I hI hS P hP

#print axioms solution
