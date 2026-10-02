import Definitions.Def_KKBinPacking_GeometricGrouping_GeomGroup
namespace KKBinPacking.GeometricGrouping
theorem geom_dominance_certificate (k : ℕ) (I : Multiset ℝ) :
    ∃ pairs : Multiset (ℝ × ℝ),
      pairs.map Prod.fst = geomJ k I ∧
      pairs.map Prod.snd ≤ I ∧
      ∀ p ∈ pairs, p.1 ≤ p.2 := by sorry
end KKBinPacking.GeometricGrouping
