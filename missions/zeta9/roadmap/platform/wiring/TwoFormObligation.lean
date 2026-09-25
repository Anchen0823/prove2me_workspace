import Mathlib

namespace ZetaNine

theorem two_independent_small_forms_of_zeta_nine :
    ∀ ε : ℝ, 0 < ε →
      ∃ b₁ a₁ b₂ a₂ : ℤ,
        b₁ * a₂ ≠ b₂ * a₁ ∧
        |(b₁ : ℝ) + (a₁ : ℝ) * (riemannZeta (9 : ℂ)).re| < ε ∧
        |(b₂ : ℝ) + (a₂ : ℝ) * (riemannZeta (9 : ℂ)).re| < ε := by sorry

end ZetaNine
