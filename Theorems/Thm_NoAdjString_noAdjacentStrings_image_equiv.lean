import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function

namespace NoAdjString

theorem noAdjacentStrings_image_equiv (n : ℕ) :
    (noAdjacentStrings n).image (boolFinsetEquiv n) = noAdjacentFinset n := by sorry

end NoAdjString
