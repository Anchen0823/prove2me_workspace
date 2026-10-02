import Mathlib
import Definitions.Def_KKBinPacking_GeometricGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP
import Definitions.Def_KKBinPacking_GeometricGrouping_GeomGroup
open KKBinPacking.Shared

namespace KKBinPacking.GeometricGrouping
theorem geomGroup_bounds (I : Multiset ℝ) (hI : IsInstance I) (hne : I ≠ 0)
    (k : ℕ) (hk : 2 ≤ k) :
    (SIZE (geomJ k I) ≤ SIZE I ∧
      SIZE I ≤ SIZE (geomJ k I) + (k : ℝ) * (2 + Real.log (1 / minSize I))) ∧
    (LIN (geomJ k I) ≤ LIN I ∧
      LIN I ≤ LIN (geomJ k I) + 2 * (k : ℝ) * (2 + Real.log (1 / minSize I))) ∧
    ((OPT (geomJ k I) : ℝ) ≤ OPT I ∧
      (OPT I : ℝ) ≤ OPT (geomJ k I) + 2 * (k : ℝ) * (2 + Real.log (1 / minSize I))) := by sorry
end KKBinPacking.GeometricGrouping
