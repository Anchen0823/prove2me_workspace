import Definitions.Def_BunkbedPercolation
open Bunkbed Finset

namespace BunkbedAux

/-- The gadget `G_n` has `2n - 1` edges. -/
theorem gadgetE_card (n : ℕ) : (gadgetE n).card = 2 * n - 1 := by
  sorry

end BunkbedAux
