import examples.«magic-squares».spencer.Aggregate

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset

namespace MagicSquaresSpencer

open MagicSquares

/-- Add one to every matrix entry. -/
def addOnes {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  fun i j => M i j + 1

/-- Subtract one from every matrix entry. -/
def subOnes {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  fun i j => M i j - 1

theorem addOnes_lineSums {n t : ℕ} {M : Matrix (Fin n) (Fin n) ℕ}
    (h : LineSums M t) : LineSums (addOnes M) (t + n) := by
  constructor
  · intro i
    simp only [addOnes, Finset.sum_add_distrib]
    rw [h.1 i]
    simp
  · intro j
    simp only [addOnes, Finset.sum_add_distrib]
    rw [h.2 j]
    simp

theorem addOnes_support {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) :
    matSupport (addOnes M) = Finset.univ := by
  classical
  ext ⟨i, j⟩
  simp [matSupport, addOnes]

theorem subOnes_addOnes {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) :
    subOnes (addOnes M) = M := by
  funext i j
  simp [subOnes, addOnes]

theorem addOnes_subOnes {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ)
    (h : matSupport M = Finset.univ) : addOnes (subOnes M) = M := by
  funext i j
  have hpos : 0 < M i j := by
    have hm : (i, j) ∈ matSupport M := by rw [h]; simp
    simpa [matSupport] using hm
  simp only [addOnes, subOnes]
  omega

theorem subOnes_lineSums {n s : ℕ} {M : Matrix (Fin n) (Fin n) ℕ}
    (h : LineSums M s) (hsup : matSupport M = Finset.univ) :
    LineSums (subOnes M) (s - n) := by
  have hback := addOnes_subOnes M hsup
  have hrow (i : Fin n) :
      (∑ j : Fin n, M i j) = (∑ j : Fin n, subOnes M i j) + n := by
    conv_lhs => rw [← hback]
    simp [addOnes, Finset.sum_add_distrib]
  have hcol (j : Fin n) :
      (∑ i : Fin n, M i j) = (∑ i : Fin n, subOnes M i j) + n := by
    conv_lhs => rw [← hback]
    simp [addOnes, Finset.sum_add_distrib]
  constructor
  · intro i
    have hi := hrow i
    rw [h.1 i] at hi
    omega
  · intro j
    have hj := hcol j
    rw [h.2 j] at hj
    omega

/-- Full-support squares at level `t+n` are exactly ordinary semi-magic squares at level `t`
after subtracting one from every entry. -/
theorem card_fullSupport_fiber_shift (n t : ℕ) :
    (matFiber n (t + n) (t + n) (Finset.univ : Finset (Fin n × Fin n))).card =
      semiMagicCount n t := by
  classical
  rw [← card_matBoxLine n t]
  refine Finset.card_bij (fun M _ => subOnes M) ?_ ?_ ?_
  · intro M hM
    rw [matFiber, Finset.mem_filter] at hM
    obtain ⟨_, hline, hsup⟩ := hM
    rw [matBoxLine, Finset.mem_filter]
    have hls : LineSums (subOnes M) t := by
      have hs := subOnes_lineSums hline hsup
      simpa using hs
    exact ⟨(mem_matBox).2 (fun i j => le_of_rowSum hls.1 i j), hls⟩
  · intro M₁ h₁ M₂ h₂ heq
    rw [matFiber, Finset.mem_filter] at h₁ h₂
    rw [← addOnes_subOnes M₁ h₁.2.2, ← addOnes_subOnes M₂ h₂.2.2, heq]
  · intro S hS
    rw [matBoxLine, Finset.mem_filter] at hS
    obtain ⟨_, hline⟩ := hS
    refine ⟨addOnes S, ?_, subOnes_addOnes S⟩
    rw [matFiber, Finset.mem_filter]
    have hs := addOnes_lineSums hline
    exact ⟨(mem_matBox).2 (fun i j => le_of_rowSum hs.1 i j), hs,
      addOnes_support S⟩

/-- A positive entry in every cell forces every row sum to be at least `n`. -/
theorem fullSupport_fiber_eq_empty_of_lt {n s : ℕ} (hs : s < n) :
    matFiber n s s (Finset.univ : Finset (Fin n × Fin n)) = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro M hM
  rw [matFiber, Finset.mem_filter] at hM
  obtain ⟨_, hline, hsup⟩ := hM
  have hback := addOnes_subOnes M hsup
  have hi := hline.1 (⟨0, by omega⟩ : Fin n)
  conv_lhs at hi => rw [← hback]
  simp [addOnes, Finset.sum_add_distrib] at hi
  omega

end MagicSquaresSpencer
