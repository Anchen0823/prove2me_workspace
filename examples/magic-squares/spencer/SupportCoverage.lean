import examples.«magic-squares».spencer.S5
import examples.«magic-squares».spencer.ClosedSupport

/-! Every occupied cell of a positive semi-magic square is covered by a permutation
whose support stays inside the square's support. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace MagicSquaresSpencer

open Finset

theorem exists_perm_support_covering_cell_of_lineSums {n s : ℕ}
    (hs : 1 ≤ s) {T : Matrix (Fin n) (Fin n) ℕ}
    (hls : LineSums T s) {e : Fin n × Fin n} (he : e ∈ matSupport T) :
    ∃ σ : Equiv.Perm (Fin n),
      e ∈ matSupport (permMatrix σ) ∧
        matSupport (permMatrix σ) ⊆ matSupport T := by
  induction s using Nat.strong_induction_on generalizing T with
  | h s ih =>
    obtain ⟨σ, hσ⟩ := exists_perm_support_subset_of_lineSums hs hls
    by_cases heσ : e ∈ matSupport (permMatrix σ)
    · exact ⟨σ, heσ, hσ⟩
    · have hpos : ∀ i, 0 < T i (σ i) :=
        (permSupport_subset_matSupport_iff T σ).mp hσ
      have he' : e ∈ matSupport (T - permMatrix σ) := by
        have hu := matSupport_sub_permMatrix_union T σ hpos
        rw [← hu] at he
        exact (Finset.mem_union.mp he).resolve_right heσ
      have hls' : LineSums (T - permMatrix σ) (s - 1) := by
        constructor
        · intro i
          rw [sum_sub_permMatrix T σ hpos i, hls.1 i]
        · intro j
          rw [sum_sub_permMatrix_col T σ hpos j, hls.2 j]
      have hs' : 1 ≤ s - 1 := by
        by_contra h
        have hz : s - 1 = 0 := by omega
        have hrow := hls'.1 e.1
        have hentry := le_of_rowSum hls'.1 e.1 e.2
        have hepos : 0 < (T - permMatrix σ) e.1 e.2 := by
          simpa [matSupport] using he'
        omega
      obtain ⟨τ, heτ, hτ⟩ := ih (s - 1) (by omega) hs' hls' he'
      exact ⟨τ, heτ, hτ.trans (matSupport_sub_permMatrix_subset T σ hpos)⟩

/-- Every edge in a support belongs to a permutation support contained in that support. -/
theorem exists_perm_support_covering_cell {n : ℕ}
    {B : Finset (Fin n × Fin n)} (hB : IsSupport n B)
    {e : Fin n × Fin n} (he : e ∈ B) :
    ∃ σ : Equiv.Perm (Fin n),
      e ∈ matSupport (permMatrix σ) ∧ matSupport (permMatrix σ) ⊆ B := by
  classical
  obtain ⟨s, hs, M, hM⟩ := hB
  rw [matFiber, Finset.mem_filter] at hM
  obtain ⟨-, hls, hsup⟩ := hM
  rw [← hsup] at he
  obtain ⟨σ, heσ, hσ⟩ := exists_perm_support_covering_cell_of_lineSums hs hls he
  exact ⟨σ, heσ, hσ.trans_eq hsup⟩

/-- All permutations whose supports lie in a board. -/
noncomputable def containedPerms (n : ℕ) (B : Finset (Fin n × Fin n)) :
    Finset (Equiv.Perm (Fin n)) := by
  classical
  exact Finset.univ.filter fun σ => matSupport (permMatrix σ) ⊆ B

theorem mem_containedPerms {n : ℕ} {B : Finset (Fin n × Fin n)}
    {σ : Equiv.Perm (Fin n)} :
    σ ∈ containedPerms n B ↔ matSupport (permMatrix σ) ⊆ B := by
  classical
  simp [containedPerms]

/-- A board covered edge by edge by contained permutations is a support. -/
theorem isSupport_of_perm_coverage {n : ℕ} (_hn : 1 ≤ n)
    {B : Finset (Fin n × Fin n)} (hne : B.Nonempty)
    (hcover : ∀ e ∈ B, ∃ σ : Equiv.Perm (Fin n),
      e ∈ matSupport (permMatrix σ) ∧ matSupport (permMatrix σ) ⊆ B) :
    IsSupport n B := by
  classical
  let P := containedPerms n B
  let M : Matrix (Fin n) (Fin n) ℕ := ∑ σ ∈ P, permMatrix σ
  have hP : P.Nonempty := by
    obtain ⟨e, he⟩ := hne
    obtain ⟨σ, -, hσ⟩ := hcover e he
    exact ⟨σ, mem_containedPerms.mpr hσ⟩
  have hs : 1 ≤ P.card := Finset.card_pos.mpr hP
  have hrow : ∀ i : Fin n, ∑ j : Fin n, M i j = P.card := by
    intro i
    simp only [M, Matrix.sum_apply]
    rw [Finset.sum_comm]
    simp [permMatrix_row]
  have hcol : ∀ j : Fin n, ∑ i : Fin n, M i j = P.card := by
    intro j
    simp only [M, Matrix.sum_apply]
    rw [Finset.sum_comm]
    simp [permMatrix_col]
  have hsupport : matSupport M = B := by
    ext e
    obtain ⟨i, j⟩ := e
    constructor
    · intro he
      have hpos : 0 < ∑ σ ∈ P, permMatrix σ i j := by
        simpa [matSupport, M, Matrix.sum_apply] using he
      obtain ⟨σ, hσ, hσpos⟩ := Finset.sum_pos_iff.mp hpos
      exact (mem_containedPerms.mp hσ) (by
        simpa [matSupport] using hσpos)
    · intro he
      obtain ⟨σ, hσpos, hσB⟩ := hcover (i, j) he
      have hσP : σ ∈ P := mem_containedPerms.mpr hσB
      have hpos : 0 < permMatrix σ i j := by
        simpa [matSupport] using hσpos
      have hsum : 0 < ∑ τ ∈ P, permMatrix τ i j :=
        Finset.sum_pos_iff.mpr ⟨σ, hσP, hpos⟩
      simpa [matSupport, M, Matrix.sum_apply] using hsum
  refine ⟨P.card, hs, M, ?_⟩
  rw [matFiber, Finset.mem_filter]
  refine ⟨?_, ⟨hrow, hcol⟩, hsupport⟩
  rw [mem_matBox]
  exact fun i j => le_of_rowSum hrow i j

/-- Positive support sets are precisely nonempty unions of contained permutation supports. -/
theorem isSupport_iff_perm_coverage {n : ℕ} (hn : 1 ≤ n)
    {B : Finset (Fin n × Fin n)} :
    IsSupport n B ↔ B.Nonempty ∧
      ∀ e ∈ B, ∃ σ : Equiv.Perm (Fin n),
        e ∈ matSupport (permMatrix σ) ∧ matSupport (permMatrix σ) ⊆ B := by
  constructor
  · intro hB
    constructor
    · obtain ⟨s, hs, M, hM⟩ := hB
      classical
      rw [matFiber, Finset.mem_filter] at hM
      obtain ⟨-, hls, hsup⟩ := hM
      obtain ⟨σ, hσ⟩ := exists_perm_support_subset_of_lineSums hs hls
      have hi : Fin n := ⟨0, hn⟩
      have he : (hi, σ hi) ∈ B := by
        rw [← hsup]
        exact hσ (mem_matSupport_permMatrix_self σ hi)
      exact ⟨_, he⟩
    · exact fun e he => exists_perm_support_covering_cell hB he
  · rintro ⟨hne, hcover⟩
    exact isSupport_of_perm_coverage hn hne hcover

end MagicSquaresSpencer
