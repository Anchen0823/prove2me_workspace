import Definitions.Def_BunkbedPercolation
open Bunkbed Finset
namespace BunkbedAux

/-- The five partition probabilities of a triple exhaust the measure. -/
theorem partition_sum_eq_total {V : Type*} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V))
    (w : Sym2 V → ℚ) (a b c : V) :
    Pabc E w a b c + Pab_c E w a b c + Pac_b E w a b c + Pa_bc E w a b c + Pa_b_c E w a b c
      = ∑ S ∈ E.powerset, weight E w S := by sorry

end BunkbedAux
