import Definitions.Def_BunkbedPercolation
open Bunkbed Finset
namespace BunkbedAux

/-- The percolation measure on a finite edge set has total mass `1`. -/
theorem sum_weight_eq_one {V : Type*} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V))
    (w : Sym2 V → ℚ) : ∑ S ∈ E.powerset, weight E w S = 1 := by sorry

end BunkbedAux
