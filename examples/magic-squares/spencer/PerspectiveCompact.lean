import Mathlib

set_option autoImplicit false

namespace MagicSquaresEuler

/-- A perspective image of a compact set is compact if its denominator stays
positive on that set. No global nonvanishing assumption is needed. -/
theorem compact_perspective_image {ι : Type*} [Fintype ι]
    (K : Set (ι → ℝ)) (q : ι → ℝ) (ℓ : (ι → ℝ) →ₗ[ℝ] ℝ)
    (hK : IsCompact K) (hpos : ∀ x ∈ K, 0 < ℓ (x - q)) :
    IsCompact ((fun x => (ℓ (x - q))⁻¹ • (x - q)) '' K) := by
  have hd : Continuous (fun x => ℓ (x - q)) :=
    ℓ.continuous_of_finiteDimensional.comp (continuous_id.sub continuous_const)
  exact hK.image_of_continuousOn
    ((hd.continuousOn.inv₀ (fun x hx => ne_of_gt (hpos x hx))).smul
      (continuous_id.sub continuous_const).continuousOn)

end MagicSquaresEuler
