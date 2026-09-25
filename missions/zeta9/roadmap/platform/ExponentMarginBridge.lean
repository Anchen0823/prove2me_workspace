import Mathlib

namespace ZetaNine

theorem exponential_margin_of_volume_and_shape (B σ : ℕ → ℝ)
    (hB : ∃ β : ℝ, β < (2641 / 250 : ℝ) ∧
      ∀ᶠ k : ℕ in Filter.atTop, B (2 * k + 2) ≤ β)
    (hS : Filter.Tendsto (fun k : ℕ => σ (2 * k + 2))
      Filter.atTop (nhds 0)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ k : ℕ in Filter.atTop,
        B (2 * k + 2) + σ (2 * k + 2) ≤ (2641 / 250 : ℝ) - ε := by sorry

end ZetaNine
