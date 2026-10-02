import Definitions.Def_KKBinPacking_GeometricGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP
open KKBinPacking.Shared

namespace KKBinPacking.GeometricGrouping
theorem size_le_lin (I : Multiset ℝ) (hI : IsInstance I) :
    SIZE I ≤ LIN I := by sorry
end KKBinPacking.GeometricGrouping
