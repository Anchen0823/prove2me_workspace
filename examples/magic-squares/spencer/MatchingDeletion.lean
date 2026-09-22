import Definitions.Def_MagicSquaresMatchingBoundary

set_option autoImplicit false

namespace MagicSquaresBoundary
open Finset
attribute [local instance] Classical.propDecidable

/-- If a matching survives outside D, deleting any selection of cells of D
cannot destroy all matchings. The whole nonempty Boolean alternating sum cancels. -/
theorem deletion_sum_eq_zero_of_complement_matching (n : ℕ)
    (D B : Finset (Fin n × Fin n)) (hD : D.Nonempty) (hmatch : HasPerm n (B \ D)) :
    (∑ S ∈ D.powerset, (-1 : ℚ) ^ S.card *
      (if HasPerm n (B \ S) then 1 else 0)) = 0 := by
  classical
  have hall (S : Finset (Fin n × Fin n)) (hS : S ∈ D.powerset) : HasPerm n (B \ S) := by
    obtain ⟨σ, hσ⟩ := hmatch
    refine ⟨σ, ?_⟩
    intro e he
    obtain ⟨heB, heD⟩ := mem_sdiff.mp (hσ he)
    exact mem_sdiff.mpr ⟨heB, fun heS => heD ((mem_powerset.mp hS) heS)⟩
  calc
    _ = ∑ S ∈ D.powerset, (-1 : ℚ) ^ S.card := by
      apply sum_congr rfl
      intro S hS
      rw [if_pos (hall S hS), mul_one]
    _ = 0 := by
      have h := sum_powerset_neg_one_pow_card_of_nonempty hD
      exact_mod_cast h

end MagicSquaresBoundary
