import Definitions.Def_BunkbedPercolation
open Bunkbed Finset SimpleGraph

namespace BunkbedAux

theorem reach_image_map {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (f : V → W) (hf : Function.Injective f) (S : Finset (Sym2 V)) (u v : V) :
    (ofEdges (S.image (Sym2.map f))).Reachable (f u) (f v) ↔ (ofEdges S).Reachable u v := by
  sorry

end BunkbedAux
