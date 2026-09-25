import Mathlib

namespace ZetaNine

theorem five_sample_sign_forces_nonzero
    (L : Polynomial ℝ →ₗ[ℝ] ℝ) (y w : Fin 5 → ℝ)
    (hy : Function.Injective y)
    (hw : ∀ j : Fin 5, 0 < w j)
    (hmom : ∀ m : ℕ, m ≤ 4 →
      L ((Polynomial.X : Polynomial ℝ) ^ m) = ∑ j : Fin 5, w j * (y j) ^ m)
    (p : Polynomial ℝ) (hpdeg : p.natDegree ≤ 4) (hp : p ≠ 0)
    (hsign : (∀ j : Fin 5, 0 ≤ p.eval (y j)) ∨ (∀ j : Fin 5, p.eval (y j) ≤ 0)) :
    L p ≠ 0 := by sorry

end ZetaNine

namespace ZetaNine

theorem min_lt_weighted_average_lt_max
    (w r : Fin 5 → ℝ) (hw : ∀ j : Fin 5, 0 < w j)
    (hsum : ∑ j : Fin 5, w j = 1)
    (hnd : ∃ j j' : Fin 5, r j ≠ r j') :
    (∃ j : Fin 5, r j < ∑ i : Fin 5, w i * r i) ∧
      (∃ j : Fin 5, (∑ i : Fin 5, w i * r i) < r j) := by sorry

end ZetaNine

namespace ZetaNine

theorem mediant_strictly_between_min_and_max
    (w a b : Fin 5 → ℝ)
    (hw : ∀ j : Fin 5, 0 < w j)
    (hb : ∀ j : Fin 5, 0 < b j)
    (hnd : ∃ j j' : Fin 5, a j / b j ≠ a j' / b j') :
    (∃ j : Fin 5,
        a j / b j < (∑ i : Fin 5, w i * a i) / (∑ i : Fin 5, w i * b i)) ∧
      (∃ j : Fin 5,
        (∑ i : Fin 5, w i * a i) / (∑ i : Fin 5, w i * b i) < a j / b j) := by sorry

end ZetaNine

namespace ZetaNine

theorem positive_matrix_maps_nonneg_to_pos
    (M : Matrix (Fin 5) (Fin 5) ℝ) (hM : ∀ i j : Fin 5, 0 < M i j)
    (v : Fin 5 → ℝ) (hv : v ≠ 0) (hvnn : ∀ i : Fin 5, 0 ≤ v i) :
    ∀ i : Fin 5, 0 < M.mulVec v i := by sorry

end ZetaNine
