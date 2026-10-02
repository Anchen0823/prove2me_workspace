import Mathlib
import Definitions.Def_KKBinPacking_GeometricGrouping_Instance
import Definitions.Def_KKBinPacking_Shared_AnyFit
open KKBinPacking.Shared

namespace KKBinPacking.GeometricGrouping
theorem anyFit_card_le (I : Multiset ℝ) (hI : IsInstance I) (g : ℝ) (hg0 : 0 < g) (hg1 : g ≤ 1)
    (P₀ : Multiset (Multiset ℝ)) (hP₀ : IsPacking (I.filter (fun x => g / 2 < x)) P₀)
    (P : Multiset (Multiset ℝ)) (hP : AnyFit P₀ (I.filter (fun x => x ≤ g / 2)) P) :
    (Multiset.card P : ℝ) ≤ max (Multiset.card P₀ : ℝ) ((1 + g) * (OPT I : ℝ) + 1) := by sorry
end KKBinPacking.GeometricGrouping
