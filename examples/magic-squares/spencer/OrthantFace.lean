import Mathlib

set_option autoImplicit false

namespace MagicSquaresGeometry

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- A sufficiently small positive multiple preserves coordinatewise domination. -/
theorem exists_pos_smul_le_of_zero_imp {ι : Type*} [Fintype ι]
    (x y : ι → 𝕜) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hzero : ∀ i, x i = 0 → y i = 0) :
    ∃ a : 𝕜, 0 < a ∧ ∀ i, a * y i ≤ x i := by
  classical
  have hfinite (s : Finset ι) : ∃ a : 𝕜, 0 < a ∧ ∀ i ∈ s, a * y i ≤ x i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨a, ha, hbound⟩ := ih
      by_cases hxi : x i = 0
      · refine ⟨a, ha, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          simp [hzero i hxi, hxi]
        · exact hbound j hj
      · obtain ⟨b, hb, hbi⟩ := exists_pos_mul_lt (lt_of_le_of_ne (hx i) (Ne.symm hxi)) (y i)
        refine ⟨min a b, lt_min ha hb, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          calc
            min a b * y i ≤ b * y i := mul_le_mul_of_nonneg_right (min_le_right _ _) (hy i)
            _ ≤ x i := by nlinarith
        · exact (mul_le_mul_of_nonneg_right (min_le_left a b) (hy j)).trans (hbound j hj)
  obtain ⟨a, ha, hab⟩ := hfinite Finset.univ
  exact ⟨a, ha, fun i => hab i (Finset.mem_univ i)⟩

/-- The nonnegative vectors in a linear subspace form a pointed cone. -/
def orthantSection {ι : Type*} (L : Submodule 𝕜 (ι → 𝕜)) :
    PointedCone 𝕜 (ι → 𝕜) :=
  PointedCone.ofSubmodule L ⊓ PointedCone.positive 𝕜 (ι → 𝕜)

theorem mem_orthantSection {ι : Type*} (L : Submodule 𝕜 (ι → 𝕜)) (x : ι → 𝕜) :
    x ∈ orthantSection L ↔ x ∈ L ∧ ∀ i, 0 ≤ x i := Iff.rfl

/-- Every face of an orthant section is closed downward under coordinate support.
This is the substantive domination step in its face/support correspondence. -/
theorem face_mem_of_zero_imp {ι : Type*} [Fintype ι]
    (L : Submodule 𝕜 (ι → 𝕜)) (F : PointedCone 𝕜 (ι → 𝕜))
    (hF : F.IsFaceOf (orthantSection L)) {x y : ι → 𝕜}
    (hx : x ∈ F) (hy : y ∈ orthantSection L)
    (hzero : ∀ i, x i = 0 → y i = 0) : y ∈ F := by
  have hxC := (mem_orthantSection L x).mp (hF.le hx)
  have hyC := (mem_orthantSection L y).mp hy
  obtain ⟨a, ha, hab⟩ := exists_pos_smul_le_of_zero_imp x y hxC.2 hyC.2 hzero
  have hz : x - a • y ∈ orthantSection L := by
    apply (mem_orthantSection L _).mpr
    refine ⟨L.sub_mem hxC.1 (L.smul_mem a hyC.1), ?_⟩
    intro i
    change 0 ≤ x i - a * y i
    exact sub_nonneg.mpr (hab i)
  apply hF.mem_of_smul_add_mem hy hz ha
  simpa using hx

end MagicSquaresGeometry
