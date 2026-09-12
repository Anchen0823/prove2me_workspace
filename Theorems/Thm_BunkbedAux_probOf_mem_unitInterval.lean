import Definitions.Def_BunkbedPercolation
open Bunkbed Finset
namespace BunkbedAux

/-- **Percolation probabilities lie in `[0,1]`.** If every edge weight is a genuine probability
then so is the probability of any event. -/
theorem probOf_mem_unitInterval {V : Type*} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V))
    (w : Sym2 V → ℚ) (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (ev : Finset (Sym2 V) → Prop) [DecidablePred ev] :
    0 ≤ probOf E w ev ∧ probOf E w ev ≤ 1 := by
  sorry

end BunkbedAux
