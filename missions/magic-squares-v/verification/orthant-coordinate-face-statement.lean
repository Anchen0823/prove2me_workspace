import Mathlib
namespace ConvexGeometry

theorem orthant_section_faces_are_coordinate_faces {𝕜 ι : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Fintype ι]
    (L : Submodule 𝕜 (ι → 𝕜)) (F : PointedCone 𝕜 (ι → 𝕜)) :
    F.IsFaceOf (PointedCone.ofSubmodule L ⊓ PointedCone.positive 𝕜 (ι → 𝕜)) ↔
      ∃ B : Set ι, ∀ x : ι → 𝕜,
        (x ∈ F ↔
          x ∈ (PointedCone.ofSubmodule L ⊓ PointedCone.positive 𝕜 (ι → 𝕜)) ∧
            ∀ i, i ∉ B → x i = 0) := by
  sorry

end ConvexGeometry
