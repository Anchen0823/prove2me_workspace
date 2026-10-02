import Definitions.Def_KKBinPacking_GeometricGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP
open KKBinPacking.Shared
namespace KKBinPacking.GeometricGrouping
theorem lin_mono_submultiset (A B : Multiset ℝ) (hA : IsInstance A) (hB : IsInstance B)
    (hAB : A ≤ B) : LIN A ≤ LIN B := by sorry
end KKBinPacking.GeometricGrouping
