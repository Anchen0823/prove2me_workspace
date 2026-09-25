import Mathlib

namespace ZetaNine

theorem irrational_of_small_nonzero_integer_forms (x : ℝ)
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ b a : ℤ,
        (b : ℝ) + (a : ℝ) * x ≠ 0 ∧
        |(b : ℝ) + (a : ℝ) * x| < ε) :
    Irrational x := by sorry

end ZetaNine

namespace ZetaNine

theorem taylor_sign_implies_kernel_sum_pos
    (R u : ℕ → ℝ) (p : Polynomial ℝ) (u₀ : ℝ)
    (hR : ∀ k : ℕ, 0 < R k)
    (hu : ∀ k : ℕ, u₀ ≤ u k)
    (hcoeff : ∀ i : ℕ, 0 ≤ (Polynomial.taylor u₀ p).coeff i)
    (hsummable : Summable (fun k : ℕ => R k * p.eval (u k)))
    (hnonzero : ∃ k : ℕ, 0 < p.eval (u k)) :
    0 < ∑' k : ℕ, R k * p.eval (u k) := by sorry

end ZetaNine

namespace ZetaNine

theorem quadrature_exact_of_moments
    (L : Polynomial ℝ →ₗ[ℝ] ℝ) (y w : Fin 5 → ℝ)
    (hmom : ∀ m : ℕ, m ≤ 4 →
      L ((Polynomial.X : Polynomial ℝ) ^ m) = ∑ j : Fin 5, w j * (y j) ^ m) :
    ∀ p : Polynomial ℝ, p.natDegree ≤ 4 →
      L p = ∑ j : Fin 5, w j * p.eval (y j) := by sorry

end ZetaNine

namespace ZetaNine

theorem exponentially_small_nonzero_forms_of_zeta_nine :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∃ b a : ℤ,
          (b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re ≠ 0 ∧
          |(b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re| <
            Real.exp (-(c * (n : ℝ))) := by sorry

end ZetaNine

namespace ZetaNine

theorem exponentially_small_independent_forms_of_zeta_nine :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∃ b₁ a₁ b₂ a₂ : ℤ,
          b₁ * a₂ ≠ b₂ * a₁ ∧
          |(b₁ : ℝ) + (a₁ : ℝ) * (riemannZeta (9 : ℂ)).re| <
            Real.exp (-(c * (n : ℝ))) ∧
          |(b₂ : ℝ) + (a₂ : ℝ) * (riemannZeta (9 : ℂ)).re| <
            Real.exp (-(c * (n : ℝ))) := by sorry

end ZetaNine
