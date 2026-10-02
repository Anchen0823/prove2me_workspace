import Definitions.Def_KKBinPacking_GeometricGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP
open KKBinPacking.Shared

namespace KKBinPacking.GeometricGrouping
theorem exists_sparse_near_optimal_lp
    (I : Multiset ℝ) (hI : IsInstance I) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : Multiset ℝ →₀ ℝ,
      IsLPFeasible I x ∧ lpCost x < LIN I + ε ∧
      x.support.card ≤ numSizes I := by sorry
end KKBinPacking.GeometricGrouping
