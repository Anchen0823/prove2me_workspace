import Mathlib

namespace Zeta9Note

theorem five_sample_sign_forces_nonzero
    (L : Polynomial ℝ →ₗ[ℝ] ℝ) (y w : Fin 5 → ℝ)
    (hy : Function.Injective y)
    (hw : ∀ j : Fin 5, 0 < w j)
    (hmom : ∀ m : ℕ, m ≤ 4 →
      L ((Polynomial.X : Polynomial ℝ) ^ m) = ∑ j : Fin 5, w j * (y j) ^ m)
    (p : Polynomial ℝ) (hpdeg : p.natDegree ≤ 4) (hp : p ≠ 0)
    (hsign : (∀ j : Fin 5, 0 ≤ p.eval (y j)) ∨ (∀ j : Fin 5, p.eval (y j) ≤ 0)) :
    L p ≠ 0 := by sorry

end Zeta9Note
