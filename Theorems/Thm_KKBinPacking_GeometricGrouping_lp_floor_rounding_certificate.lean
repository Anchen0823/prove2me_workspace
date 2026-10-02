import Definitions.Def_KKBinPacking_GeometricGrouping_Algorithm2
open KKBinPacking.Shared

namespace KKBinPacking.GeometricGrouping
theorem lp_floor_rounding_certificate
    (I : Multiset ℝ) (hI : IsInstance I)
    (x : Multiset ℝ →₀ ℝ) (hx : IsLPFeasible I x) :
    let R := I - (principalConfigs x).join
    ∃ P : Multiset (Multiset ℝ),
      IsPacking (I - R) P ∧
      P.card ≤ principalCount x ∧
      SIZE R ≤ lpCost x - (principalCount x : ℝ) ∧
      (OPT R : ℝ) ≤ (x.support.card : ℝ) := by sorry
end KKBinPacking.GeometricGrouping
