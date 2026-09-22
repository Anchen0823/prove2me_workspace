import examples.«magic-squares».spencer.OrthantCoordinateFace

set_option autoImplicit false

namespace MagicSquaresGeometry

variable {𝕜 ι : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [Fintype ι]

/-- Coordinates used by at least one point of a cone. -/
noncomputable def faceSupport (F : PointedCone 𝕜 (ι → 𝕜)) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => ∃ x ∈ F, x i ≠ 0

theorem mem_faceSupport (F : PointedCone 𝕜 (ι → 𝕜)) (i : ι) :
    i ∈ faceSupport F ↔ ∃ x ∈ F, x i ≠ 0 := by
  classical
  simp [faceSupport]

theorem exists_faceSupport_witness (L : Submodule 𝕜 (ι → 𝕜))
    (F : PointedCone 𝕜 (ι → 𝕜)) (hF : F.IsFaceOf (orthantSection L)) :
    ∃ x ∈ F, ∀ i, i ∈ faceSupport F ↔ x i ≠ 0 := by
  obtain ⟨x, hx, hmax⟩ := exists_max_support_point L F hF
  refine ⟨x, hx, fun i => ?_⟩
  rw [mem_faceSupport]
  constructor
  · rintro ⟨y, hy, hiy⟩ hix
    exact hiy (hmax y hy i hix)
  · exact fun hix => ⟨x, hx, hix⟩

theorem face_eq_coordinateFace_support (L : Submodule 𝕜 (ι → 𝕜))
    (F : PointedCone 𝕜 (ι → 𝕜)) (hF : F.IsFaceOf (orthantSection L)) :
    F = coordinateFace L (↑(faceSupport F) : Set ι) := by
  obtain ⟨x, hx, hchar⟩ := exists_face_zero_characterization L F hF
  ext y
  rw [mem_coordinateFace, hchar y]
  constructor
  · rintro ⟨hy, hzero⟩
    refine ⟨hy, fun i hi => ?_⟩
    apply hzero i
    by_contra hxi
    exact hi ((mem_faceSupport F i).mpr ⟨x, hx, hxi⟩)
  · rintro ⟨hy, hzero⟩
    refine ⟨hy, fun i hxi => ?_⟩
    apply hzero i
    intro hi
    obtain ⟨z, hz, hzi⟩ := (mem_faceSupport F i).mp hi
    exact hzi (((hchar z).mp hz).2 i hxi)

theorem face_le_iff_support_subset (L : Submodule 𝕜 (ι → 𝕜))
    (F G : PointedCone 𝕜 (ι → 𝕜))
    (hF : F.IsFaceOf (orthantSection L)) (hG : G.IsFaceOf (orthantSection L)) :
    F ≤ G ↔ faceSupport F ⊆ faceSupport G := by
  constructor
  · intro h i hi
    obtain ⟨x, hx, hxi⟩ := (mem_faceSupport F i).mp hi
    exact (mem_faceSupport G i).mpr ⟨x, h hx, hxi⟩
  · intro h x hx
    rw [face_eq_coordinateFace_support L G hG, mem_coordinateFace]
    refine ⟨hF.le hx, fun i hi => ?_⟩
    by_contra hxi
    exact hi (h ((mem_faceSupport F i).mpr ⟨x, hx, hxi⟩))

/-- The entire face order embeds into the Boolean order on coordinates. -/
noncomputable def faceSupportOrderEmbedding (L : Submodule 𝕜 (ι → 𝕜)) :
    {F : PointedCone 𝕜 (ι → 𝕜) // F.IsFaceOf (orthantSection L)} ↪o Finset ι where
  toFun F := faceSupport F.val
  inj' := by
    intro F G h
    change faceSupport F.val = faceSupport G.val at h
    apply Subtype.ext
    apply le_antisymm
    · exact (face_le_iff_support_subset L F.val G.val F.property G.property).mpr
        (by rw [h])
    · exact (face_le_iff_support_subset L G.val F.val G.property F.property).mpr
        (by rw [h])
  map_rel_iff' := by
    intro F G
    exact (face_le_iff_support_subset L F.val G.val F.property G.property).symm

theorem finite_faces_orthantSection (L : Submodule 𝕜 (ι → 𝕜)) :
    Finite {F : PointedCone 𝕜 (ι → 𝕜) // F.IsFaceOf (orthantSection L)} :=
  Finite.of_injective (faceSupportOrderEmbedding L) (faceSupportOrderEmbedding L).injective

/-- The coordinate supports actually realized by points of the orthant section. -/
def RealizedSupport (L : Submodule 𝕜 (ι → 𝕜)) (B : Finset ι) : Prop :=
  ∃ x ∈ orthantSection L, ∀ i, i ∈ B ↔ x i ≠ 0

theorem faceSupport_coordinateFace (L : Submodule 𝕜 (ι → 𝕜))
    (B : Finset ι) (hB : RealizedSupport L B) :
    faceSupport (coordinateFace L (↑B : Set ι)) = B := by
  classical
  obtain ⟨x, hx, hs⟩ := hB
  have hxF : x ∈ coordinateFace L (↑B : Set ι) := by
    refine ⟨hx, fun i hi => ?_⟩
    by_contra hxi
    exact hi ((hs i).mpr hxi)
  ext i
  rw [mem_faceSupport]
  constructor
  · rintro ⟨y, hy, hyi⟩
    by_contra hi
    exact hyi (hy.2 i hi)
  · exact fun hi => ⟨x, hxF, (hs i).mp hi⟩

/-- The face lattice and the order of realized coordinate supports agree exactly. -/
noncomputable def faceSupportOrderIso (L : Submodule 𝕜 (ι → 𝕜)) :
    {F : PointedCone 𝕜 (ι → 𝕜) // F.IsFaceOf (orthantSection L)} ≃o
      {B : Finset ι // RealizedSupport L B} where
  toFun F := ⟨faceSupport F.val, by
    obtain ⟨x, hx, hs⟩ := exists_faceSupport_witness L F.val F.property
    exact ⟨x, F.property.le hx, hs⟩⟩
  invFun B := ⟨coordinateFace L (↑B.val : Set ι), coordinateFace_isFaceOf L _⟩
  left_inv F := by
    apply Subtype.ext
    exact (face_eq_coordinateFace_support L F.val F.property).symm
  right_inv B := by
    apply Subtype.ext
    exact faceSupport_coordinateFace L B.val B.property
  map_rel_iff' := by
    intro F G
    exact (face_le_iff_support_subset L F.val G.val F.property G.property).symm

end MagicSquaresGeometry
