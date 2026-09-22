import examples.«magic-squares».spencer.OrthantFaceOrder
import examples.«magic-squares».spencer.SemiMagicCone
import examples.«magic-squares».spencer.DoublyStochasticSupport

set_option autoImplicit false

namespace MagicSquaresGeometry

open Finset MagicSquaresBoundary
attribute [local instance] Classical.propDecidable

/-- Nonzero supports of the semi-magic cone are precisely matching-covered boards. -/
theorem realizedSupport_semiMagic_iff (n : ℕ) (hn : 1 ≤ n)
    (B : Finset (Fin n × Fin n)) :
    RealizedSupport (semiMagicSubspace n) B ↔ B = ∅ ∨ MatchingCoveredBoard n B := by
  classical
  constructor
  · rintro ⟨x, hx, hB⟩
    obtain ⟨hxL, hxpos⟩ := (mem_orthantSection _ _).mp hx
    by_cases hx0 : x = 0
    · left
      ext e
      simp only [Finset.notMem_empty, iff_false]
      intro he
      have hne := (hB e).mp he
      simpa [hx0] using hne
    · right
      obtain ⟨s, hs, hrow, hcol⟩ :=
        exists_pos_common_line_sum_of_nonneg_ne_zero hxL hxpos hx0
      have hM := normalizedSemiMagic_mem_doublyStochastic hs hxpos hrow hcol
      have hc := matchingCovered_positive_support n hn (normalizedSemiMagic x s) hM
      have heq : (Finset.univ.filter
          (fun e : Fin n × Fin n => 0 < normalizedSemiMagic x s e.1 e.2)) = B := by
        ext e
        simp only [mem_filter, mem_univ, true_and]
        rw [normalizedSemiMagic_pos_iff hs]
        exact (show 0 < x e ↔ x e ≠ 0 from
          ⟨ne_of_gt, fun he => lt_of_le_of_ne (hxpos e) (Ne.symm he)⟩).trans (hB e).symm
      rwa [heq] at hc
  · rintro (rfl | hB)
    · exact ⟨0, (orthantSection (semiMagicSubspace n)).zero_mem, by simp⟩
    · obtain ⟨M, hM, hMB⟩ := exists_doublyStochastic_with_positive_support n B hB
      refine ⟨fun e => M e.1 e.2, ?_, ?_⟩
      · apply (mem_orthantSection _ _).mpr
        exact ⟨⟨1, sum_row_of_mem_doublyStochastic hM,
          sum_col_of_mem_doublyStochastic hM⟩, fun e => nonneg_of_mem_doublyStochastic hM⟩
      · intro e
        exact (hMB e.1 e.2).symm.trans
          ⟨ne_of_gt, fun he => lt_of_le_of_ne (nonneg_of_mem_doublyStochastic hM) (Ne.symm he)⟩

/-- The face order of the nonnegative semi-magic cone is the matching-board order,
with the empty board as its bottom element. -/
noncomputable def semiMagicFaceSupportOrderIso (n : ℕ) (hn : 1 ≤ n) :
    {F : PointedCone ℝ ((Fin n × Fin n) → ℝ) //
      F.IsFaceOf (orthantSection (semiMagicSubspace n))} ≃o
    {B : Finset (Fin n × Fin n) // B = ∅ ∨ MatchingCoveredBoard n B} :=
  (faceSupportOrderIso (semiMagicSubspace n)).trans
    { toFun := fun B => ⟨B.val, (realizedSupport_semiMagic_iff n hn B.val).mp B.property⟩
      invFun := fun B => ⟨B.val, (realizedSupport_semiMagic_iff n hn B.val).mpr B.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }

end MagicSquaresGeometry
