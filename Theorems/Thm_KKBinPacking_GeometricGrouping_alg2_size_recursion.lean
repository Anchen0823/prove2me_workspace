import Mathlib
import Definitions.Def_KKBinPacking_GeometricGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP
import Definitions.Def_KKBinPacking_Shared_AnyFit
import Definitions.Def_KKBinPacking_GeometricGrouping_GeomGroup
import Definitions.Def_KKBinPacking_GeometricGrouping_Algorithm2
open KKBinPacking.Shared

namespace KKBinPacking.GeometricGrouping
theorem alg2_size_recursion (k : ℕ) (hk : 2 ≤ k) (g : ℝ) (hg0 : 0 < g) (hg1 : g ≤ 1)
    (I : Multiset ℝ) (hI : IsInstance I) (tr : Alg2Trace k g I) (i : ℕ) (hi : i < tr.t) :
    SIZE (tr.inst (i + 1)) ≤ LIN (tr.inst (i + 1)) ∧
      LIN (tr.inst (i + 1)) ≤ ∑ c ∈ (tr.x i).support, (tr.x i c - (⌊tr.x i c⌋₊ : ℝ)) ∧
      ∑ c ∈ (tr.x i).support, (tr.x i c - (⌊tr.x i c⌋₊ : ℝ)) ≤ numSizes (geomJ k (tr.inst i)) ∧
      (numSizes (geomJ k (tr.inst i)) : ℝ) ≤ SIZE (tr.inst i) / k + Real.log (1 / g) ∧
      SIZE (tr.inst (i + 1)) ≤ SIZE (tr.inst i) / k + Real.log (1 / g) := by sorry
end KKBinPacking.GeometricGrouping
