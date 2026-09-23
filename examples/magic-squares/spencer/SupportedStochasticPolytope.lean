import Mathlib

set_option autoImplicit false

namespace MagicSquaresGeometry

open Finset Matrix

attribute [local instance] Classical.propDecidable

/-- The affine equations for doubly stochastic matrices whose entries outside
`B` vanish.  This affine subspace is allowed to be empty. -/
def supportedStochasticAffine (n : ℕ) (B : Finset (Fin n × Fin n)) :
    AffineSubspace ℝ ((Fin n × Fin n) → ℝ) where
  carrier := {x |
    (∀ i, ∑ j, x (i, j) = 1) ∧
    (∀ j, ∑ i, x (i, j) = 1) ∧
    ∀ e ∉ B, x e = 0}
  smul_vsub_vadd_mem' c x y z hx hy hz := by
    rcases hx with ⟨hxr, hxc, hxo⟩
    rcases hy with ⟨hyr, hyc, hyo⟩
    rcases hz with ⟨hzr, hzc, hzo⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i
      simp only [vsub_eq_sub, vadd_eq_add, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, sum_add_distrib, sum_sub_distrib, ← mul_sum]
      rw [hxr i, hyr i, hzr i]
      ring
    · intro j
      simp only [vsub_eq_sub, vadd_eq_add, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, sum_add_distrib, sum_sub_distrib, ← mul_sum]
      rw [hxc j, hyc j, hzc j]
      ring
    · intro e he
      simp only [vsub_eq_sub, vadd_eq_add, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [hxo e he, hyo e he, hzo e he]
      ring

@[simp] theorem mem_supportedStochasticAffine_iff (n : ℕ)
    (B : Finset (Fin n × Fin n)) (x : (Fin n × Fin n) → ℝ) :
    x ∈ supportedStochasticAffine n B ↔
      (∀ i, ∑ j, x (i, j) = 1) ∧
      (∀ j, ∑ i, x (i, j) = 1) ∧
      ∀ e ∉ B, x e = 0 :=
  Iff.rfl

/-- Membership in the supported nonnegative affine section is precisely
doubly stochasticity together with vanishing outside the support board. -/
theorem mem_supportedStochasticPolytope_iff (n : ℕ)
    (B : Finset (Fin n × Fin n)) (x : (Fin n × Fin n) → ℝ) :
    (x ∈ supportedStochasticAffine n B ∧ ∀ e, 0 ≤ x e) ↔
      Matrix.of (fun i j => x (i, j)) ∈
          doublyStochastic ℝ (Fin n) ∧
        ∀ e ∉ B, x e = 0 := by
  rw [mem_doublyStochastic_iff_sum]
  simp only [mem_supportedStochasticAffine_iff]
  aesop

/-- The polytope of nonnegative doubly stochastic matrices supported in `B`
is compact. -/
theorem supportedStochasticPolytope_isCompact (n : ℕ)
    (B : Finset (Fin n × Fin n)) :
    IsCompact {x : (Fin n × Fin n) → ℝ |
      x ∈ supportedStochasticAffine n B ∧ ∀ e, 0 ≤ x e} := by
  let C : Set ((Fin n × Fin n) → ℝ) := {x |
    x ∈ supportedStochasticAffine n B ∧ ∀ e, 0 ≤ x e}
  let Q : Set ((Fin n × Fin n) → ℝ) :=
    Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)
  have hclosed_nonneg : IsClosed {x : (Fin n × Fin n) → ℝ | ∀ e, 0 ≤ x e} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun e => isClosed_Ici.preimage (continuous_apply e)
  have hclosed : IsClosed C :=
    (supportedStochasticAffine n B).closed_of_finiteDimensional.inter hclosed_nonneg
  have hcompactQ : IsCompact Q := isCompact_univ_pi fun _ => isCompact_Icc
  have hsubset : C ⊆ Q := by
    intro x hx
    have hmem : Matrix.of (fun i j => x (i, j)) ∈
        doublyStochastic ℝ (Fin n) :=
      (mem_supportedStochasticPolytope_iff n B x).mp hx |>.1
    intro e he
    exact ⟨hx.2 e, le_one_of_mem_doublyStochastic hmem⟩
  exact IsCompact.of_isClosed_subset hcompactQ hclosed hsubset

end MagicSquaresGeometry
