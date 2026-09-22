import Mathlib

namespace MagicSquaresRealCone

/-- Real matrices whose row and column sums share one common value. -/
def balancedSubspace (n : ℕ) : Submodule ℝ ((Fin n × Fin n) → ℝ) where
  carrier := {x | ∃ s : ℝ,
    (∀ i, ∑ j, x (i, j) = s) ∧ (∀ j, ∑ i, x (i, j) = s)}
  zero_mem' := by
    refine ⟨0, ?_, ?_⟩ <;> intro i <;> simp
  add_mem' := by
    rintro x y ⟨sx, hxr, hxc⟩ ⟨sy, hyr, hyc⟩
    refine ⟨sx + sy, ?_, ?_⟩
    · intro i
      simp only [Pi.add_apply, Finset.sum_add_distrib, hxr i, hyr i]
    · intro j
      simp only [Pi.add_apply, Finset.sum_add_distrib, hxc j, hyc j]
  smul_mem' := by
    rintro a x ⟨s, hxr, hxc⟩
    refine ⟨a * s, ?_, ?_⟩
    · intro i
      change ∑ j, a * x (i, j) = a * s
      rw [← Finset.mul_sum, hxr i]
    · intro j
      change ∑ i, a * x (i, j) = a * s
      rw [← Finset.mul_sum, hxc j]

/-- The cone of real nonnegative matrices with balanced row and column sums. -/
def cone (n : ℕ) : PointedCone ℝ ((Fin n × Fin n) → ℝ) :=
  PointedCone.ofSubmodule (balancedSubspace n) ⊓
    PointedCone.positive ℝ ((Fin n × Fin n) → ℝ)

end MagicSquaresRealCone
