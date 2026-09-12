import Definitions.Def_BunkbedHypergraph
open Bunkbed Bunkbed.Hyper SimpleGraph Finset
namespace BunkbedFalse

/-- **Lemma 4.1** (hyperedge simulation, p. 7). -/
theorem hyperedge_simulation (n : ℕ) (P : ℚ) (hn : 3 ≤ n) (hP0 : 0 < P) (hP1 : P < 1) :
    Pab_c (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) = Pac_b (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) ∧
    Pabc (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) * Pa_b_c (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) - Pab_c (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) * Pac_b (gadgetE n) (gadgetW n P) 0 1 (Fin.last n)
      > (n * (1 - P) / (1 + P) - 1) * Pa_bc (gadgetE n) (gadgetW n P) 0 1 (Fin.last n) := by sorry

end BunkbedFalse
