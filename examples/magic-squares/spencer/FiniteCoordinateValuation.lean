import examples.«magic-squares».spencer.CompactConvexValuation

set_option autoImplicit false

namespace MagicSquaresEuler

attribute [local instance] Classical.propDecidable

/-- A finite coordinate type can be reindexed by `Fin` without changing the
Euler relation for compact convex indicators. -/
theorem finiteCoordinate_indicator_relation (η : Type*) [Fintype η]
    {α : Type*} [Fintype α] (K : α → Set (η → ℝ)) (w : α → ℚ)
    (hc : ∀ i, IsCompact (K i)) (hv : ∀ i, Convex ℝ (K i))
    (h : ∀ x, (∑ i, if x ∈ K i then w i else 0) = 0) :
    (∑ i, if (K i).Nonempty then w i else 0) = 0 := by
  classical
  let e : (Fin (Fintype.card η) → ℝ) ≃L[ℝ] (η → ℝ) :=
    ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : η => ℝ) (Fintype.equivFin η).symm
  let K' : α → Set (Fin (Fintype.card η) → ℝ) := fun i => e.symm '' K i
  have hc' : ∀ i, IsCompact (K' i) := fun i => (hc i).image e.symm.continuous
  have hv' : ∀ i, Convex ℝ (K' i) := fun i => (hv i).linear_image e.symm.toLinearMap
  have h' : ∀ x, (∑ i, if x ∈ K' i then w i else 0) = 0 := by
    intro x
    have hs (i : α) : x ∈ K' i ↔ e x ∈ K i := by
      simp only [K', Set.mem_image]
      constructor
      · rintro ⟨y, hy, hxy⟩
        simpa [← hxy] using hy
      · intro hx
        exact ⟨e x, hx, e.symm_apply_apply x⟩
    simpa only [hs] using h (e x)
  have ht := compactConvex_indicator_relation (Fintype.card η) K' w hc' hv' h'
  simpa only [K', Set.image_nonempty] using ht

end MagicSquaresEuler
