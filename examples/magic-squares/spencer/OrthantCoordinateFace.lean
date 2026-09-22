import examples.«magic-squares».spencer.OrthantFace
import examples.«magic-squares».spencer.OrthantFaceSupport

set_option autoImplicit false

namespace MagicSquaresGeometry

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Impose additional coordinate zeros on an orthant section. -/
def coordinateFace {ι : Type*} (L : Submodule 𝕜 (ι → 𝕜)) (B : Set ι) :
    PointedCone 𝕜 (ι → 𝕜) where
  carrier := {x | x ∈ orthantSection L ∧ ∀ i, i ∉ B → x i = 0}
  zero_mem' := ⟨(orthantSection L).zero_mem, by simp⟩
  add_mem' := by
    intro x y hx hy
    refine ⟨(orthantSection L).add_mem hx.1 hy.1, ?_⟩
    intro i hi
    change x i + y i = 0
    rw [hx.2 i hi, hy.2 i hi, add_zero]
  smul_mem' := by
    intro a x hx
    refine ⟨(orthantSection L).smul_mem a.property hx.1, ?_⟩
    intro i hi
    change (a : 𝕜) * x i = 0
    rw [hx.2 i hi, mul_zero]

theorem mem_coordinateFace {ι : Type*} (L : Submodule 𝕜 (ι → 𝕜)) (B : Set ι)
    (x : ι → 𝕜) :
    x ∈ coordinateFace L B ↔ x ∈ orthantSection L ∧ ∀ i, i ∉ B → x i = 0 := Iff.rfl

/-- Nonnegativity makes every additional zero-coordinate constraint a face. -/
theorem coordinateFace_isFaceOf {ι : Type*} (L : Submodule 𝕜 (ι → 𝕜)) (B : Set ι) :
    (coordinateFace L B).IsFaceOf (orthantSection L) := by
  constructor
  · exact fun _ hx => hx.1
  · intro x y a hx hy ha hsum
    refine ⟨hx, ?_⟩
    intro i hi
    have hxi := ((mem_orthantSection L x).mp hx).2 i
    have hyi := ((mem_orthantSection L y).mp hy).2 i
    have heq := hsum.2 i hi
    change a * x i + y i = 0 at heq
    nlinarith

theorem isFaceOf_iff_coordinateFace {ι : Type*} [Fintype ι]
    (L : Submodule 𝕜 (ι → 𝕜)) (F : PointedCone 𝕜 (ι → 𝕜)) :
    F.IsFaceOf (orthantSection L) ↔ ∃ B : Set ι, F = coordinateFace L B := by
  constructor
  · intro hF
    obtain ⟨x, hx, hchar⟩ := exists_face_zero_characterization L F hF
    refine ⟨{i | x i ≠ 0}, ?_⟩
    ext y
    rw [mem_coordinateFace, hchar y]
    simp
  · rintro ⟨B, rfl⟩
    exact coordinateFace_isFaceOf L B

end MagicSquaresGeometry
