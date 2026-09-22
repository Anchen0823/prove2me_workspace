import Mathlib

set_option autoImplicit false

namespace MagicSquaresGeometry

/-- Every positive entry of a doubly stochastic matrix lies in the positive
support of one entire permutation. -/
theorem exists_positive_permutation_through_entry (n : ℕ)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M ∈ doublyStochastic ℝ (Fin n))
    (i j : Fin n) (hij : 0 < M i j) :
    ∃ σ : Equiv.Perm (Fin n), σ i = j ∧ ∀ k, 0 < M k (σ k) := by
  classical
  obtain ⟨w, hw, -, hsum⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
  have hperm (σ : Equiv.Perm (Fin n)) (k l : Fin n) :
      σ.permMatrix ℝ k l = if σ k = l then 1 else 0 := by
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      eq_comm]
  have hentry (k l : Fin n) :
      M k l = ∑ σ : Equiv.Perm (Fin n), w σ * σ.permMatrix ℝ k l := by
    rw [← hsum]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have hterm_nonneg (σ : Equiv.Perm (Fin n)) (k l : Fin n) :
      0 ≤ w σ * σ.permMatrix ℝ k l := by
    rw [hperm]
    split_ifs <;> nlinarith [hw σ]
  have hsumpos :
      0 < ∑ σ : Equiv.Perm (Fin n), w σ * σ.permMatrix ℝ i j := by
    rw [← hentry]
    exact hij
  obtain ⟨σ, -, hσpos⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun σ _ => hterm_nonneg σ i j)).mp hsumpos
  have hσij : σ i = j := by
    by_contra hne
    rw [hperm, if_neg hne, mul_zero] at hσpos
    exact (lt_irrefl (0 : ℝ)) hσpos
  have hwσ : 0 < w σ := by
    simpa [hperm, hσij] using hσpos
  refine ⟨σ, hσij, ?_⟩
  intro k
  have hle :
      w σ * σ.permMatrix ℝ k (σ k) ≤
        ∑ τ : Equiv.Perm (Fin n), w τ * τ.permMatrix ℝ k (σ k) :=
    Finset.single_le_sum (fun τ _ => hterm_nonneg τ k (σ k)) (Finset.mem_univ σ)
  rw [hperm, if_pos rfl, mul_one, ← hentry] at hle
  exact lt_of_lt_of_le hwσ hle

end MagicSquaresGeometry
