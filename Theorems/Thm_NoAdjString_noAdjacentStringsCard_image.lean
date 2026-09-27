import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function

namespace NoAdjString

theorem noAdjacentStringsCard_image (n k : ℕ) :
    (noAdjacentStringsCard n k).image (boolFinsetEquiv n) = noAdjacentFinsetCard n k := by sorry

end NoAdjString
