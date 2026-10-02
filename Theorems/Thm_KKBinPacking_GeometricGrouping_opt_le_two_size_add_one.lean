import Mathlib
import Definitions.Def_KKBinPacking_GeometricGrouping_Instance

namespace KKBinPacking.GeometricGrouping
theorem opt_le_two_size_add_one (I : Multiset ℝ) (hI : IsInstance I) :
    (OPT I : ℝ) ≤ 2 * SIZE I + 1 := by sorry
end KKBinPacking.GeometricGrouping
