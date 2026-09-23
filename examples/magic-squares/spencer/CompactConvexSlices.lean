import Mathlib

set_option autoImplicit false

namespace MagicSquaresEuler

/-- The slice of a set in `n + 1` coordinates obtained by fixing coordinate
zero to be `t`. -/
def coordinateSlice (n : ℕ) (K : Set (Fin (n + 1) → ℝ)) (t : ℝ) :
    Set (Fin n → ℝ) :=
  {y | Fin.cons t y ∈ K}

theorem compact_coordinateSlice (n : ℕ) (K : Set (Fin (n + 1) → ℝ))
    (t : ℝ) (hK : IsCompact K) : IsCompact (coordinateSlice n K t) := by
  have hclosed : IsClosed {x : Fin (n + 1) → ℝ | x 0 = t} := by
    exact isClosed_singleton.preimage (continuous_apply 0)
  have heq : coordinateSlice n K t =
      (fun x : Fin (n + 1) → ℝ => Fin.tail x) ''
        (K ∩ {x : Fin (n + 1) → ℝ | x 0 = t}) := by
    ext y
    constructor
    · intro hy
      refine ⟨Fin.cons t y, ⟨hy, ?_⟩, ?_⟩
      · simp
      · simp
    · rintro ⟨x, ⟨hxK, hx0⟩, rfl⟩
      have hx : Fin.cons t (Fin.tail x) = x := by
        rw [← hx0]
        exact Fin.cons_self_tail x
      change Fin.cons t (Fin.tail x) ∈ K
      rwa [hx]
  rw [heq]
  exact (hK.inter_right hclosed).image continuous_id.finTail

theorem convex_coordinateSlice (n : ℕ) (K : Set (Fin (n + 1) → ℝ))
    (t : ℝ) (hK : Convex ℝ K) : Convex ℝ (coordinateSlice n K t) := by
  intro x hx y hy a b ha hb hab
  have hmem := hK hx hy ha hb hab
  show Fin.cons t (a • x + b • y) ∈ K
  convert hmem using 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← add_mul, hab, one_mul]
  · simp

theorem slice_nonempty_iff (n : ℕ) (K : Set (Fin (n + 1) → ℝ)) (t : ℝ) :
    (coordinateSlice n K t).Nonempty ↔ t ∈ (fun x => x 0) '' K := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨Fin.cons t y, hy, by simp⟩
  · rintro ⟨x, hxK, hx0⟩
    refine ⟨Fin.tail x, ?_⟩
    have hx : Fin.cons t (Fin.tail x) = x := by
      rw [← hx0]
      exact Fin.cons_self_tail x
    change Fin.cons t (Fin.tail x) ∈ K
    rwa [hx]

end MagicSquaresEuler
