import examples.«magic-squares».spencer.CompactRealValuation

set_option autoImplicit false

namespace MagicSquaresEuler

attribute [local instance] Classical.propDecidable

theorem compact_coordinateProjection (n : ℕ) (K : Set (Fin (n + 1) → ℝ))
    (hK : IsCompact K) : IsCompact ((fun x => x 0) '' K) :=
  hK.image (continuous_apply 0)

theorem convex_coordinateProjection (n : ℕ) (K : Set (Fin (n + 1) → ℝ))
    (hK : Convex ℝ K) : Convex ℝ ((fun x => x 0) '' K) :=
  hK.linear_image (LinearMap.proj 0)

/-- In dimension zero there is one point, so the relation follows by evaluation. -/
theorem zeroDim_indicator_relation {ι : Type*} [Fintype ι]
    (K : ι → Set (Fin 0 → ℝ)) (w : ι → ℚ)
    (h : ∀ x, (∑ i, if x ∈ K i then w i else 0) = 0) :
    (∑ i, if (K i).Nonempty then w i else 0) = 0 := by
  classical
  have heq (i : ι) : (K i).Nonempty ↔ (fun _ => (0 : ℝ)) ∈ K i := by
    constructor
    · rintro ⟨x, hx⟩
      have hx0 : x = fun _ => (0 : ℝ) := Subsingleton.elim _ _
      simpa only [hx0] using hx
    · intro hi
      exact ⟨_, hi⟩
  simpa only [heq] using h (fun _ => 0)

end MagicSquaresEuler
