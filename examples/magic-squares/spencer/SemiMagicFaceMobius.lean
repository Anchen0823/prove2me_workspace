import examples.«magic-squares».spencer.MatchingMobius
import examples.«magic-squares».spencer.FiniteMobiusTransport
import examples.«magic-squares».spencer.SemiMagicFaceSupport

set_option autoImplicit false

namespace MagicSquaresGeometry

attribute [local instance] Classical.propDecidable

abbrev SemiMagicFace (n : ℕ) :=
  {F : PointedCone ℝ ((Fin n × Fin n) → ℝ) //
    F.IsFaceOf (orthantSection (semiMagicSubspace n))}

noncomputable instance semiMagicFaceFintype (n : ℕ) : Fintype (SemiMagicFace n) := by
  letI := finite_faces_orthantSection (semiMagicSubspace n)
  exact Fintype.ofFinite _

noncomputable instance semiMagicFaceOrderBot (n : ℕ) : OrderBot (SemiMagicFace n) where
  bot := ⟨coordinateFace (semiMagicSubspace n) ∅,
    coordinateFace_isFaceOf (semiMagicSubspace n) ∅⟩
  bot_le F := by
    intro x hx
    have hx0 : x = 0 := by
      funext i
      exact hx.2 i (by simp)
    simpa [hx0] using F.val.zero_mem

noncomputable instance semiMagicFaceLocallyFiniteOrder (n : ℕ) :
    LocallyFiniteOrder (SemiMagicFace n) := Fintype.toLocallyFiniteOrder

/-- The public matching coefficient of a nonzero face is its negative bottom
Mobius number in the actual geometric face poset. -/
theorem matchingCoefficient_face_eq_neg_mu (n : ℕ) (hn : 1 ≤ n)
    (F : SemiMagicFace n) (hF : F ≠ ⊥) :
    MagicSquaresBoundary.matchingEulerCoefficient n (faceSupport F.val) =
      -IncidenceAlgebra.mu ℚ (⊥ : SemiMagicFace n) F := by
  classical
  let e : SemiMagicFace n ≃o MagicSquaresBoundary.MatchingBoard n :=
    semiMagicFaceSupportOrderIso n hn
  have heF : e F ≠ ⊥ := by
    intro he
    apply hF
    apply e.injective
    simpa using he
  have hc := MagicSquaresBoundary.matchingEulerCoefficient_eq_neg_mu n hn (e F) heF
  have hm := mobius_from_bottom_orderIso e F
  rw [hm] at hc
  exact hc

end MagicSquaresGeometry
