import Definitions.Def_BunkbedSubstituted
open Bunkbed Bunkbed.Hyper Bunkbed.Sub

/-- Exact boundary-law transfer for the six substituted gadgets (GPZ, Section 4.2). -/
theorem BunkbedFalse.sub_probability_transfer (P : WZ → ℚ)
    (habc : P .abc = Pabc (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hab : P .ab_c = Pab_c (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hac : P .ac_b = Pac_b (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hbc : P .a_bc = Pa_bc (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (hsep : P .a_b_c = Pa_b_c (gadgetE 1204) (gadgetW 1204 (1/2)) 0 1 (Fin.last 1204))
    (x y : Fin 10) (l : Fin 2) :
    bbProb subEdges (fun _ => (1/2 : ℚ)) subT (iota x, 0) (iota y, l) =
      wzProb hollomTriple hollomT P (x, 0) (y, l) := by sorry
