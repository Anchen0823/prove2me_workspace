import Definitions.Def_KKBinPacking_GeometricGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP
open KKBinPacking.Shared

namespace KKBinPacking.GeometricGrouping
theorem lin_le_opt (I : Multiset ℝ) (hI : IsInstance I) : LIN I ≤ (OPT I : ℝ) := by sorry
end KKBinPacking.GeometricGrouping
