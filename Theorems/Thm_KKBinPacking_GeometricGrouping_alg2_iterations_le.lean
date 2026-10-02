import Mathlib
import Definitions.Def_KKBinPacking_GeometricGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP
import Definitions.Def_KKBinPacking_Shared_AnyFit
import Definitions.Def_KKBinPacking_GeometricGrouping_GeomGroup
import Definitions.Def_KKBinPacking_GeometricGrouping_Algorithm2
open KKBinPacking.Shared

namespace KKBinPacking.GeometricGrouping
theorem alg2_iterations_le (k : ℕ) (hk : 2 ≤ k) (g : ℝ) (hg0 : 0 < g) (hg1 : g ≤ 1)
    (I : Multiset ℝ) (hI : IsInstance I) (tr : Alg2Trace k g I) (ht : 1 ≤ tr.t) :
    (tr.t : ℝ) ≤ Real.log (SIZE (tr.inst 0)) / Real.log k + 1 := by sorry
end KKBinPacking.GeometricGrouping
