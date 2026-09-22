import examples.«magic-squares».spencer.BirkhoffSupport
import Definitions.Def_MagicSquaresMatchingBoundary

set_option autoImplicit false

namespace MagicSquaresGeometry

open Finset MagicSquaresBoundary
attribute [local instance] Classical.propDecidable

/-- The positive support of a real doubly stochastic matrix is matching-covered. -/
theorem matchingCovered_positive_support (n : ℕ) (hn : 1 ≤ n)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M ∈ doublyStochastic ℝ (Fin n)) :
    MatchingCoveredBoard n
      ((Finset.univ : Finset (Fin n × Fin n)).filter (fun e => 0 < M e.1 e.2)) := by
  classical
  let B : Finset (Fin n × Fin n) :=
    (Finset.univ : Finset (Fin n × Fin n)).filter (fun e => 0 < M e.1 e.2)
  have hnonneg (j : Fin n) : 0 ≤ M ⟨0, hn⟩ j :=
    nonneg_of_mem_doublyStochastic hM
  have hrow : 0 < ∑ j : Fin n, M ⟨0, hn⟩ j := by
    rw [sum_row_of_mem_doublyStochastic hM]
    norm_num
  obtain ⟨j, _, hj⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun j _ => hnonneg j)).mp hrow
  change MatchingCoveredBoard n B
  constructor
  · exact ⟨(⟨0, hn⟩, j), by simp [B, hj]⟩
  · intro e he
    obtain ⟨i, j⟩ := e
    have hij : 0 < M i j := by simpa [B] using he
    obtain ⟨σ, hσij, hσpos⟩ := exists_positive_permutation_through_entry n M hM i j hij
    refine ⟨σ, ?_, ?_⟩
    · simp [permSupport, ← hσij]
    · intro p hp
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hp
      simp [B, hσpos k]

/-- Every matching-covered board is exactly the positive support of a real
doubly stochastic matrix. -/
theorem exists_doublyStochastic_with_positive_support (n : ℕ)
    (B : Finset (Fin n × Fin n)) (hB : MatchingCoveredBoard n B) :
    ∃ M : Matrix (Fin n) (Fin n) ℝ,
      M ∈ doublyStochastic ℝ (Fin n) ∧
        ∀ i j : Fin n, 0 < M i j ↔ (i, j) ∈ B := by
  classical
  let P : Finset (Equiv.Perm (Fin n)) :=
    Finset.univ.filter (fun σ => permSupport σ ⊆ B)
  obtain ⟨e, he⟩ := hB.1
  obtain ⟨τ, _, hτB⟩ := hB.2 e he
  have hτP : τ ∈ P := by simp [P, hτB]
  have hP : P.Nonempty := ⟨τ, hτP⟩
  let w : ℝ := (P.card : ℝ)⁻¹
  have hw : 0 < w := by
    dsimp [w]
    exact inv_pos.mpr (by exact_mod_cast Finset.card_pos.mpr hP)
  have hwsum : ∑ σ ∈ P, w = 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    dsimp [w]
    exact mul_inv_cancel₀ (by exact_mod_cast Finset.card_ne_zero_of_mem hτP)
  let M : Matrix (Fin n) (Fin n) ℝ :=
    ∑ σ ∈ P, w • σ.permMatrix ℝ
  have hM : M ∈ doublyStochastic ℝ (Fin n) := by
    apply convex_doublyStochastic.sum_mem
    · exact fun _ _ => hw.le
    · exact hwsum
    · exact fun _ _ => permMatrix_mem_doublyStochastic
  have hperm (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
      σ.permMatrix ℝ i j = if σ i = j then 1 else 0 := by
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      eq_comm]
  have hentry (i j : Fin n) :
      M i j = ∑ σ ∈ P, w * σ.permMatrix ℝ i j := by
    simp only [M, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have hterm_nonneg (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
      0 ≤ w * σ.permMatrix ℝ i j := by
    rw [hperm]
    split_ifs <;> nlinarith [hw.le]
  refine ⟨M, hM, ?_⟩
  intro i j
  constructor
  · intro hij
    have hsumpos : 0 < ∑ σ ∈ P, w * σ.permMatrix ℝ i j := by
      rw [← hentry]
      exact hij
    obtain ⟨σ, hσP, hσpos⟩ :=
      (Finset.sum_pos_iff_of_nonneg (fun σ _ => hterm_nonneg σ i j)).mp hsumpos
    have hσij : σ i = j := by
      by_contra hne
      rw [hperm, if_neg hne, mul_zero] at hσpos
      exact (lt_irrefl (0 : ℝ)) hσpos
    have hσB : permSupport σ ⊆ B := by simpa [P] using hσP
    apply hσB
    simp [permSupport, hσij]
  · intro hij
    obtain ⟨σ, hcell, hσB⟩ := hB.2 (i, j) hij
    have hσP : σ ∈ P := by simp [P, hσB]
    have hσij : σ i = j := by
      simpa [permSupport] using hcell
    have hle : w * σ.permMatrix ℝ i j ≤
        ∑ ρ ∈ P, w * ρ.permMatrix ℝ i j :=
      Finset.single_le_sum (fun ρ _ => hterm_nonneg ρ i j) hσP
    rw [hperm, if_pos hσij, mul_one, ← hentry] at hle
    exact lt_of_lt_of_le hw hle

end MagicSquaresGeometry
