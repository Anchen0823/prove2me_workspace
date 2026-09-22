import examples.«magic-squares».spencer.OrthantFace

set_option autoImplicit false

namespace MagicSquaresGeometry

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Every face has a point that uses every coordinate used anywhere in the face. -/
theorem exists_max_support_point {ι : Type*} [Fintype ι]
    (L : Submodule 𝕜 (ι → 𝕜)) (F : PointedCone 𝕜 (ι → 𝕜))
    (hF : F.IsFaceOf (orthantSection L)) :
    ∃ x : ι → 𝕜, x ∈ F ∧
      ∀ y : ι → 𝕜, y ∈ F → ∀ i, x i = 0 → y i = 0 := by
  classical
  have hchoice (i : ι) : ∃ v : ι → 𝕜, v ∈ F ∧
      (∀ y : ι → 𝕜, y ∈ F → y i ≠ 0 → v i ≠ 0) := by
    by_cases h : ∃ y : ι → 𝕜, y ∈ F ∧ y i ≠ 0
    · obtain ⟨y, hy, hyi⟩ := h
      exact ⟨y, hy, fun _ _ _ => hyi⟩
    · refine ⟨0, F.zero_mem, ?_⟩
      intro y hy hyi
      exact False.elim (h ⟨y, hy, hyi⟩)
  choose v hvF hvcover using hchoice
  let x : ι → 𝕜 := ∑ i : ι, v i
  have hx : x ∈ F := F.sum_mem (fun i _ => hvF i)
  refine ⟨x, hx, ?_⟩
  intro y hy i hxi
  by_contra hyi
  have hvi : v i i ≠ 0 := hvcover i y hy hyi
  have hnonneg (j : ι) : 0 ≤ v j i :=
    ((mem_orthantSection L (v j)).mp (hF.le (hvF j))).2 i
  have hle : v i i ≤ x i := by
    change v i i ≤ (∑ j : ι, v j) i
    rw [Finset.sum_apply]
    exact Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
  have hzero : v i i = 0 := le_antisymm (hxi ▸ hle) (hnonneg i)
  exact hvi hzero

/-- Faces of an orthant section are exactly its members with fixed zero coordinates. -/
theorem exists_face_zero_characterization {ι : Type*} [Fintype ι]
    (L : Submodule 𝕜 (ι → 𝕜)) (F : PointedCone 𝕜 (ι → 𝕜))
    (hF : F.IsFaceOf (orthantSection L)) :
    ∃ x : ι → 𝕜, x ∈ F ∧ ∀ y : ι → 𝕜,
      (y ∈ F ↔ y ∈ orthantSection L ∧ ∀ i, x i = 0 → y i = 0) := by
  obtain ⟨x, hx, hmax⟩ := exists_max_support_point L F hF
  refine ⟨x, hx, fun y => ?_⟩
  constructor
  · intro hy
    exact ⟨hF.le hy, hmax y hy⟩
  · rintro ⟨hy, hzero⟩
    exact face_mem_of_zero_imp L F hF hx hy hzero

end MagicSquaresGeometry
