import Definitions.Def_BunkbedSubstituted
open Bunkbed Bunkbed.Sub Finset

namespace BunkbedFalse

/-- Distinct copies of `G_1204` in the substituted graph have disjoint edge sets. -/
theorem sub_gadget_copies_disjoint :
    ∀ i j : Fin 6, i ≠ j →
      Disjoint ((gadgetE 1204).image (Sym2.map (emb i)))
        ((gadgetE 1204).image (Sym2.map (emb j))) := by
  sorry

end BunkbedFalse
