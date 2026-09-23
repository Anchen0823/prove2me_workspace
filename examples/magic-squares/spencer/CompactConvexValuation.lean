import examples.«magic-squares».spencer.CompactConvexProjection
import examples.«magic-squares».spencer.CompactConvexSlices

set_option autoImplicit false

namespace MagicSquaresEuler

attribute [local instance] Classical.propDecidable

/-- Euler integration is well-defined on finite rational linear combinations
of compact convex indicators in every finite real coordinate space. -/
theorem compactConvex_indicator_relation (n : ℕ)
    {ι : Type*} [Fintype ι] (K : ι → Set (Fin n → ℝ)) (w : ι → ℚ)
    (hc : ∀ i, IsCompact (K i)) (hv : ∀ i, Convex ℝ (K i))
    (h : ∀ x, (∑ i, if x ∈ K i then w i else 0) = 0) :
    (∑ i, if (K i).Nonempty then w i else 0) = 0 := by
  classical
  induction n generalizing ι with
  | zero => exact zeroDim_indicator_relation K w h
  | succ n ih =>
    let P : ι → Set ℝ := fun i => (fun x => x 0) '' K i
    have hp : ∀ t : ℝ, (∑ i, if t ∈ P i then w i else 0) = 0 := by
      intro t
      have hs := ih (fun i => coordinateSlice n (K i) t) w
        (fun i => compact_coordinateSlice n (K i) t (hc i))
        (fun i => convex_coordinateSlice n (K i) t (hv i))
        (fun y => h (Fin.cons t y))
      simpa only [slice_nonempty_iff, P] using hs
    have htotal := compactReal_indicator_relation P w
      (fun i => compact_coordinateProjection n (K i) (hc i))
      (fun i => convex_coordinateProjection n (K i) (hv i)) hp
    simpa only [P, Set.image_nonempty] using htotal

end MagicSquaresEuler
