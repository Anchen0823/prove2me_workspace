import Definitions.Def_BunkbedSubstituted
open Bunkbed Bunkbed.Hyper Finset SimpleGraph
namespace BunkbedFalse

/-- **The invariants of the substituted graph.** It has 14442 edges, its transversal set has three
vertices, and it is connected. -/
theorem sub_invariants :
    (ofEdges Bunkbed.Sub.subEdges).edgeFinset.card = 14442 ∧ Bunkbed.Sub.subT.card = 3
      ∧ (ofEdges Bunkbed.Sub.subEdges).Connected := by
  sorry

end BunkbedFalse
