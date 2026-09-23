import examples.«magic-squares».spencer.PerspectiveCancellation
import examples.«magic-squares».spencer.PerspectiveExternalPoint

set_option autoImplicit false

namespace MagicSquaresEuler

attribute [local instance] Classical.propDecidable

/-- Two nested positive supports in a compact affine orthant section give the
coordinate-face cancellation required by the matching-boundary reduction. -/
theorem affineOrthant_support_extension_cancellation {ι : Type*} [Fintype ι]
    (A : AffineSubspace ℝ (ι → ℝ)) (D : Finset ι)
    (hK : IsCompact {x : ι → ℝ | x ∈ A ∧ ∀ i, 0 ≤ x i})
    (x y : ι → ℝ) (hxA : x ∈ A) (hyA : y ∈ A)
    (hxpos : ∀ i ∈ D, 0 < x i) (hxzero : ∀ i, i ∉ D → x i = 0)
    (hy : ∀ i, 0 ≤ y i) (hnew : ∃ i, i ∉ D ∧ 0 < y i) :
    (∑ S ∈ D.powerset, if
      ({z : ι → ℝ | (z ∈ A ∧ ∀ i, 0 ≤ z i) ∧ ∀ i ∈ S, z i = 0}).Nonempty
      then (-1 : ℚ) ^ S.card else 0) = 0 := by
  classical
  obtain ⟨q, hqA, hqpos, hqneg, hqout⟩ :=
    exists_affine_external_point A D x y hxA hyA hxpos hxzero hy hnew
  have hnegative : ∃ i, q i < 0 := by
    by_contra hn
    push_neg at hn
    exact hqout hn
  obtain ⟨i, hi⟩ := hnegative
  apply affineOrthant_coordinate_cancellation A D q (LinearMap.proj i) hK hqA
    hqout hqpos hqneg
  intro z hzA hz
  change 0 < z i - q i
  linarith [hz i]

end MagicSquaresEuler
