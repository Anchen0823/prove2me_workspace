import Mathlib

namespace ZetaNine

theorem irrational_of_two_small_integer_forms (x : ℝ)
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ b₁ a₁ b₂ a₂ : ℤ,
        b₁ * a₂ ≠ b₂ * a₁ ∧
        |(b₁ : ℝ) + (a₁ : ℝ) * x| < ε ∧
        |(b₂ : ℝ) + (a₂ : ℝ) * x| < ε) :
    Irrational x := by sorry

end ZetaNine
