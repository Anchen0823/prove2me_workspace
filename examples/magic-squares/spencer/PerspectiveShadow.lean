import examples.«magic-squares».spencer.PerspectiveCoverage
import examples.«magic-squares».spencer.PerspectiveCompact
import examples.«magic-squares».spencer.PerspectiveConvex

set_option autoImplicit false

namespace MagicSquaresEuler

theorem perspective_constant_on_ray {ι : Type*}
    (q x : ι → ℝ) (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ) (t : ℝ)
    (ht : t ≠ 0) (hd : ℓ (x - q) ≠ 0) :
    (ℓ ((q + t • (x - q)) - q))⁻¹ • ((q + t • (x - q)) - q) =
      (ℓ (x - q))⁻¹ • (x - q) := by
  have he : (q + t • (x - q)) - q = t • (x - q) := by abel
  rw [he, map_smul]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

/-- The far coordinate boundary has the same perspective shadow as the whole
compact affine orthant section. -/
theorem perspective_shadow_eq_backBoundary {ι : Type*} [Fintype ι]
    (A : AffineSubspace ℝ (ι → ℝ)) (D : Set ι) (q : ι → ℝ)
    (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ)
    (hK : IsCompact {x : ι → ℝ | x ∈ A ∧ ∀ i, 0 ≤ x i})
    (hqA : q ∈ A) (hqout : ¬ ∀ i, 0 ≤ q i)
    (hqD : ∀ i, i ∉ D → q i ≤ 0)
    (hpos : ∀ x : ι → ℝ, x ∈ A → (∀ i, 0 ≤ x i) → 0 < ℓ (x - q)) :
    (fun x => (ℓ (x - q))⁻¹ • (x - q)) ''
      ({x : ι → ℝ | x ∈ A ∧ ∀ i, 0 ≤ x i} ∩ coordinateBackBoundary D) =
    (fun x => (ℓ (x - q))⁻¹ • (x - q)) ''
      {x : ι → ℝ | x ∈ A ∧ ∀ i, 0 ≤ x i} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx.1, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, ht, hyA, hy, hyD⟩ :=
      affine_orthant_ray_hits_backBoundary A D q hK hqA hqout hqD x hx.1 hx.2
    refine ⟨q + t • (x - q), ⟨⟨hyA, hy⟩, hyD⟩, ?_⟩
    exact perspective_constant_on_ray q x ℓ t (by linarith)
      (ne_of_gt (hpos x hx.1 hx.2))

end MagicSquaresEuler
