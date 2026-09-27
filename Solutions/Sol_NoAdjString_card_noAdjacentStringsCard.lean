import Theorems.Thm_NoAdjString_noAdjacentStringsCard_image
import Theorems.Thm_NoAdjString_card_noAdjacentFinsetCard
import Definitions.Def_NoAdjacentBinaryStrings

open Finset Function NoAdjString

theorem solution (n k : ℕ) :
    (noAdjacentStringsCard n k).card = Nat.choose (n + 1 - k) k := by
  have h_img := noAdjacentStringsCard_image n k
  have hc : (noAdjacentStringsCard n k).card =
      ((noAdjacentStringsCard n k).image (boolFinsetEquiv n)).card := by
    rw [Finset.card_image_of_injective _ (boolFinsetEquiv n).injective]
  rw [hc, h_img, card_noAdjacentFinsetCard]
