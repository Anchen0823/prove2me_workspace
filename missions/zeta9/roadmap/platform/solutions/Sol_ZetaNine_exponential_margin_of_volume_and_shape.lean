import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

open Filter

theorem solution (B σ : ℕ → ℝ)
    (hB : ∃ β : ℝ, β < (2641 / 250 : ℝ) ∧
      ∀ᶠ k : ℕ in Filter.atTop, B (2 * k + 2) ≤ β)
    (hS : Filter.Tendsto (fun k : ℕ => σ (2 * k + 2))
      Filter.atTop (nhds 0)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ k : ℕ in Filter.atTop,
        B (2 * k + 2) + σ (2 * k + 2) ≤ (2641 / 250 : ℝ) - ε := by
  obtain ⟨β, hβ, hB⟩ := hB
  let ε : ℝ := ((2641 / 250 : ℝ) - β) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hσ : ∀ᶠ k : ℕ in Filter.atTop, σ (2 * k + 2) < ε :=
    (tendsto_order.1 hS).2 ε hε
  refine ⟨ε, hε, ?_⟩
  filter_upwards [hB, hσ] with k hBk hσk
  dsimp [ε] at hσk ⊢
  linarith
