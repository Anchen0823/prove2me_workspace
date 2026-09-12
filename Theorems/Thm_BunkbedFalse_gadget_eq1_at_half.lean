import Definitions.Def_BunkbedPercolation
open Bunkbed Finset
namespace BunkbedFalse

/-- **The gadget at `P = 1/2` and `n = 1204` satisfies Eq. [1].** The three partition-probability
conditions required by the robustness lemma -- symmetry, strict positivity of the determinant, and
Eq. [1] with the constant 400 -- all hold for `G_1204` under `1/2`-percolation. -/
theorem gadget_eq1_at_half :
    Pab_c (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
        = Pac_b (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
    ∧ 0 < Pabc (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
          * Pa_b_c (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
        - Pab_c (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
          * Pac_b (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
    ∧ 400 * Pa_bc (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
        ≤ Pabc (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
          * Pa_b_c (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
        - Pab_c (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
          * Pac_b (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204) := by
  sorry

end BunkbedFalse
