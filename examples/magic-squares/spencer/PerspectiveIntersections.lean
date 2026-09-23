import examples.«magic-squares».spencer.PerspectiveShadow

set_option autoImplicit false

namespace MagicSquaresEuler

theorem perspective_injOn_backBoundary {ι : Type*}
    (D : Set ι) (q : ι → ℝ) (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ)
    (hq : ∀ i ∈ D, 0 < q i) :
    Set.InjOn (fun x => (ℓ (x - q))⁻¹ • (x - q))
      {x | x ∈ coordinateBackBoundary D ∧ 0 < ℓ (x - q)} := by
  intro x hx y hy heq
  apply coordinateBackBoundary_normalize_injOn D q (fun x => ℓ (x - q)) hq hx hy
  funext i
  have hi := congrFun heq i
  simpa only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, div_eq_mul_inv, mul_comm] using hi

/-- Perspective images commute with all finite coordinate-face intersections,
including the empty intersection relative to `P`. -/
theorem perspective_image_coordinate_intersections {ι : Type*} [DecidableEq ι]
    (P : Set (ι → ℝ)) (D S : Finset ι) (q : ι → ℝ)
    (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ) (hSD : S ⊆ D)
    (hP : ∀ x ∈ P, ∀ i ∈ D, 0 ≤ x i)
    (hq : ∀ i ∈ D, 0 < q i) (hpos : ∀ x ∈ P, 0 < ℓ (x - q)) :
    (fun x => (ℓ (x - q))⁻¹ • (x - q)) '' {x | x ∈ P ∧ ∀ i ∈ S, x i = 0} =
      {z | z ∈ (fun x => (ℓ (x - q))⁻¹ • (x - q)) '' P ∧
        ∀ i ∈ S, z ∈ (fun x => (ℓ (x - q))⁻¹ • (x - q)) ''
          {x | x ∈ P ∧ x i = 0}} := by
  classical
  ext z
  constructor
  · rintro ⟨x, ⟨hx, hzero⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, fun i hi => ⟨x, ⟨hx, hzero i hi⟩, rfl⟩⟩
  · rintro ⟨⟨x, hx, hfx⟩, hfaces⟩
    by_cases hS : S = ∅
    · exact ⟨x, ⟨hx, by simp [hS]⟩, hfx⟩
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      obtain ⟨y, ⟨hyP, hyi⟩, hfy⟩ := hfaces i hi
      refine ⟨y, ⟨hyP, ?_⟩, hfy⟩
      intro j hj
      obtain ⟨v, ⟨hvP, hvj⟩, hfv⟩ := hfaces j hj
      have hyv : y = v := by
        apply perspective_injOn_backBoundary (↑D : Set ι) q ℓ hq
          ⟨⟨hP y hyP, i, hSD hi, hyi⟩, hpos y hyP⟩
          ⟨⟨hP v hvP, j, hSD hj, hvj⟩, hpos v hvP⟩
        exact hfy.trans hfv.symm
      simpa only [hyv] using hvj

end MagicSquaresEuler
