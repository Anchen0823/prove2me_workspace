import Definitions.Def_BunkbedPercolation
open Bunkbed Finset SimpleGraph

namespace BunkbedAux

theorem probOf_image_map {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (f : V → W) (hf : Function.Injective f) (E : Finset (Sym2 V)) (c : ℚ)
    (ev : Finset (Sym2 V) → Prop) [DecidablePred ev]
    (ev' : Finset (Sym2 W) → Prop) [DecidablePred ev']
    (hev : ∀ S, S ⊆ E → (ev S ↔ ev' (S.image (Sym2.map f)))) :
    probOf E (fun _ => c) ev = probOf (E.image (Sym2.map f)) (fun _ => c) ev' := by
  sorry

end BunkbedAux
