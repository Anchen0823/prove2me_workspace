import Mathlib

namespace ZetaNine

theorem exponentially_small_nonzero_forms_of_zeta_nine :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∃ b a : ℤ,
          (b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re ≠ 0 ∧
          |(b : ℝ) + (a : ℝ) * (riemannZeta (9 : ℂ)).re| <
            Real.exp (-(c * (n : ℝ))) := by sorry

end ZetaNine
