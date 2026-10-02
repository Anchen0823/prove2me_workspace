import Mathlib
import Definitions.Def_KKBinPacking_GeometricGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP
open KKBinPacking.Shared

namespace KKBinPacking.GeometricGrouping
theorem size_le_lin_le_opt_le_lin_add (I : Multiset ℝ) (hI : IsInstance I) :
    SIZE I ≤ LIN I ∧ LIN I ≤ (OPT I : ℝ) ∧
      (OPT I : ℝ) ≤ LIN I + ((numSizes I : ℝ) + 1) / 2 := by sorry
end KKBinPacking.GeometricGrouping
