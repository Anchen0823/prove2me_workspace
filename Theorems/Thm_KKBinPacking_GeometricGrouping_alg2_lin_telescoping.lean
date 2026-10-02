import Mathlib
import Definitions.Def_KKBinPacking_GeometricGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP
import Definitions.Def_KKBinPacking_Shared_AnyFit
import Definitions.Def_KKBinPacking_GeometricGrouping_GeomGroup
import Definitions.Def_KKBinPacking_GeometricGrouping_Algorithm2
open KKBinPacking.Shared

namespace KKBinPacking.GeometricGrouping
theorem alg2_lin_telescoping (k : ℕ) (hk : 2 ≤ k) (g : ℝ) (hg0 : 0 < g)
    (I : Multiset ℝ) (hI : IsInstance I) (tr : Alg2Trace k g I) :
    (∀ i < tr.t,
      LIN (tr.inst (i + 1)) ≤ LIN (geomJ k (tr.inst i)) + 1 - principalCount (tr.x i) ∧
        LIN (geomJ k (tr.inst i)) + 1 - principalCount (tr.x i) ≤
          LIN (tr.inst i) + 1 - principalCount (tr.x i)) ∧
    ((∑ i ∈ Finset.range tr.t, principalCount (tr.x i) : ℕ) : ℝ) ≤
      LIN (geomJ k (tr.inst 0)) + tr.t := by sorry
end KKBinPacking.GeometricGrouping
