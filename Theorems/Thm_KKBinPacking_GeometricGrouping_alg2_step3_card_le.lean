import Mathlib
import Definitions.Def_KKBinPacking_GeometricGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_ConfigLP
import Definitions.Def_KKBinPacking_Shared_AnyFit
import Definitions.Def_KKBinPacking_GeometricGrouping_GeomGroup
import Definitions.Def_KKBinPacking_GeometricGrouping_Algorithm2
open KKBinPacking.Shared

namespace KKBinPacking.GeometricGrouping
theorem alg2_step3_card_le (k : ℕ) (hk : 2 ≤ k) (g : ℝ) (hg0 : 0 < g)
    (I : Multiset ℝ) (hI : IsInstance I) (tr : Alg2Trace k g I) :
    IsPacking (I.filter (fun p => g < p)) (alg2Step3Bins tr.t tr.Bp tr.PJ' tr.P3) ∧
    (Multiset.card (alg2Step3Bins tr.t tr.Bp tr.PJ' tr.P3) : ℝ) ≤
      ((∑ i ∈ Finset.range tr.t, principalCount (tr.x i) : ℕ) : ℝ) +
        tr.t * (2 * (k : ℝ) * (2 + Real.log (1 / g))) +
        2 + (2 / (1 - 1 / (k : ℝ))) * Real.log (1 / g) := by sorry
end KKBinPacking.GeometricGrouping
