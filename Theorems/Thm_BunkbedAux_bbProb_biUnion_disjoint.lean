import Definitions.Def_BunkbedPercolation
open Bunkbed Finset SimpleGraph

namespace BunkbedAux

theorem bbProb_biUnion_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → Finset (Sym2 V)) (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j))
    (w : Sym2 V → ℚ) (T : Finset V) (x y : V × Fin 2) :
    bbProb (Finset.univ.biUnion E) w T x y
      = ∑ S₀ ∈ Fintype.piFinset (fun i => (E i).powerset),
          ∑ S₁ ∈ Fintype.piFinset (fun i => (E i).powerset),
            (if (bbGraph T (Finset.univ.biUnion (fun i => S₀ i))
                  (Finset.univ.biUnion (fun i => S₁ i))).Reachable x y then (1 : ℚ) else 0)
              * (∏ i, weight (E i) w (S₀ i)) * (∏ i, weight (E i) w (S₁ i)) := by
  sorry

end BunkbedAux
