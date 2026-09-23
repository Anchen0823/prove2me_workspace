import Mathlib

set_option autoImplicit false

namespace MagicSquaresEuler

/-- Normalizing an affine translate of a convex set by a positive linear
functional preserves convexity. -/
theorem convex_perspective_image {ι : Type*} (K : Set (ι → ℝ)) (q : ι → ℝ)
    (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ) (hK : Convex ℝ K)
    (hpos : ∀ x ∈ K, 0 < ℓ (x - q)) :
    Convex ℝ ((fun x => (ℓ (x - q))⁻¹ • (x - q)) '' K) := by
  intro X hX Y hY a b ha hb hab
  rcases hX with ⟨x, hx, rfl⟩
  rcases hY with ⟨y, hy, rfl⟩
  let dx : ℝ := ℓ (x - q)
  let dy : ℝ := ℓ (y - q)
  have hdx : 0 < dx := hpos x hx
  have hdy : 0 < dy := hpos y hy
  let r : ℝ := a * dy + b * dx
  have hr : 0 < r := by
    dsimp only [r]
    have hane : 0 < a ∨ 0 < b := by
      rcases lt_or_eq_of_le ha with ha' | rfl
      · exact Or.inl ha'
      · right
        linarith
    rcases hane with ha' | hb'
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hdy) (mul_nonneg hb hdx.le)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg ha hdy.le) (mul_pos hb' hdx)
  let t : ℝ := a * dy / r
  let u : ℝ := b * dx / r
  have ht : 0 ≤ t := div_nonneg (mul_nonneg ha hdy.le) hr.le
  have hu : 0 ≤ u := div_nonneg (mul_nonneg hb hdx.le) hr.le
  have htu : t + u = 1 := by
    dsimp only [t, u, r]
    rw [← add_div]
    exact div_self (ne_of_gt hr)
  let z : ι → ℝ := t • x + u • y
  have hz : z ∈ K := hK hx hy ht hu htu
  refine ⟨z, hz, ?_⟩
  have hzq : z - q = t • (x - q) + u • (y - q) := by
    funext i
    simp only [z, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    calc
      t * x i + u * y i - q i = t * x i + u * y i - (t + u) * q i := by rw [htu, one_mul]
      _ = t * (x i - q i) + u * (y i - q i) := by ring
  have hℓz : ℓ (z - q) = dx * dy / r := by
    rw [hzq, ℓ.map_add, ℓ.map_smul, ℓ.map_smul]
    simp only [smul_eq_mul]
    change t * dx + u * dy = dx * dy / r
    dsimp only [t, u]
    field_simp [ne_of_gt hr]
    nlinarith [hab]
  change (ℓ (z - q))⁻¹ • (z - q) =
    a • ((ℓ (x - q))⁻¹ • (x - q)) + b • ((ℓ (y - q))⁻¹ • (y - q))
  rw [hℓz, hzq]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  change (dx * dy / r)⁻¹ * (t * (x i - q i) + u * (y i - q i)) =
    a * (dx⁻¹ * (x i - q i)) + b * (dy⁻¹ * (y i - q i))
  dsimp only [t, u]
  have hdx0 : dx ≠ 0 := ne_of_gt hdx
  have hdy0 : dy ≠ 0 := ne_of_gt hdy
  field_simp [hdx0, hdy0, ne_of_gt hr]

end MagicSquaresEuler
