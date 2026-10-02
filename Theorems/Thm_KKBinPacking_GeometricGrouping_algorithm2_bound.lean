import Mathlib
import Definitions.Def_KKBinPacking_GeometricGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP
import Definitions.Def_KKBinPacking_Shared_AnyFit
import Definitions.Def_KKBinPacking_GeometricGrouping_GeomGroup
import Definitions.Def_KKBinPacking_GeometricGrouping_Algorithm2
open KKBinPacking.Shared

namespace KKBinPacking.GeometricGrouping
theorem algorithm2_bound (k : ℕ) (hk : 2 ≤ k) (g : ℝ) (hg0 : 0 < g) (hg1 : g ≤ 1 / 2)
    (I : Multiset ℝ) (hI : IsInstance I) (hS : 1 ≤ SIZE I)
    (P : Multiset (Multiset ℝ)) (hP : Alg2Run k g I P) :
    IsPacking I P ∧
      (Multiset.card P : ℝ) ≤
        max ((1 + 2 * g) * (OPT I : ℝ) + 1)
          ((OPT I : ℝ) + (1 + Real.log (SIZE I) / Real.log k) *
              (1 + 4 * (k : ℝ) + 2 * (k : ℝ) * Real.log (1 / g)) +
            2 + (2 / (1 - 1 / (k : ℝ))) * Real.log (1 / g)) := by sorry
end KKBinPacking.GeometricGrouping
