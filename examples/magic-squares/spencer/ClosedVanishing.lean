import examples.«magic-squares».spencer.ClosedEvaluation
import examples.«magic-squares».spencer.CyclicPermutations

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace MagicSquaresSpencer

open Finset Polynomial

def HasDisjointPerms (n : ℕ) (B : Finset (Fin n × Fin n)) (k : ℕ) : Prop :=
  ∃ σ : Fin k → Equiv.Perm (Fin n),
    (∀ i, matSupport (permMatrix (σ i)) ⊆ B) ∧
    ∀ i j, i ≠ j → Disjoint (matSupport (permMatrix (σ i)))
      (matSupport (permMatrix (σ j)))

theorem HasDisjointPerms.mono_count {n k l : ℕ} {B : Finset (Fin n × Fin n)}
    (h : HasDisjointPerms n B l) (hkl : k ≤ l) : HasDisjointPerms n B k := by
  obtain ⟨σ, hσ, hd⟩ := h
  refine ⟨fun i => σ (Fin.castLE hkl i), fun i => hσ _, ?_⟩
  intro i j hij
  apply hd
  intro heq
  exact hij (Fin.ext (congrArg (fun x : Fin l => x.val) heq))

theorem HasDisjointPerms.hasPerm {n k : ℕ} {B : Finset (Fin n × Fin n)}
    (h : HasDisjointPerms n B k) (hk : 1 ≤ k) : HasPerm n B := by
  obtain ⟨σ, hσ, -⟩ := h
  exact ⟨σ ⟨0, hk⟩, hσ _⟩

theorem disjointPerms_remove {n k : ℕ} {B S : Finset (Fin n × Fin n)}
    (σ : Fin (k + 1) → Equiv.Perm (Fin n))
    (hσ : ∀ i, matSupport (permMatrix (σ i)) ⊆ B)
    (hd : ∀ i j, i ≠ j → Disjoint (matSupport (permMatrix (σ i)))
      (matSupport (permMatrix (σ j))))
    (hS : S ⊆ matSupport (permMatrix (σ (Fin.last k)))) :
    HasDisjointPerms n (B \ S) k := by
  refine ⟨fun i => σ i.castSucc, ?_, ?_⟩
  · intro i p hp
    refine Finset.mem_sdiff.mpr ⟨hσ _ hp, ?_⟩
    intro hpS
    exact Finset.disjoint_left.mp
      (hd i.castSucc (Fin.last k) (Fin.castSucc_ne_last i)) hp (hS hpS)
  · intro i j hij
    apply hd
    intro heq
    exact hij (Fin.ext (congrArg (fun x : Fin (k + 1) => x.val) heq))

/-- A board containing `k+1` disjoint permutations has a counting-polynomial
zero at `-k`. No reciprocity theorem is used. -/
theorem closedPoly_neg_eq_zero_of_disjointPerms (n : ℕ) (hn : 1 ≤ n) :
    ∀ k : ℕ, 1 ≤ k → ∀ B : Finset (Fin n × Fin n),
      HasDisjointPerms n B (k + 1) → (closedPoly n B).eval (-(k : ℚ)) = 0 := by
  classical
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro hk B hpack
    obtain ⟨σ, hσ, hd⟩ := hpack
    let φ := matSupport (permMatrix (σ (Fin.last (k + 1))))
    have hB : HasPerm n B := ⟨σ (Fin.last (k + 1)), hσ _⟩
    have hchild : ∀ S ∈ φ.powerset.filter (·.Nonempty),
        HasDisjointPerms n (B \ S) (k + 1) := by
      intro S hS
      exact disjointPerms_remove σ hσ hd (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)
    have hrec := closedPoly_recurrence n B (σ (Fin.last (k + 1))) (hσ _)
      (-((k + 1 : ℕ) : ℚ))
    have harg : -((k + 1 : ℕ) : ℚ) + 1 = -(k : ℚ) := by push_cast; ring
    rw [harg] at hrec
    by_cases hk0 : k = 0
    · subst k
      have hφ : φ.Nonempty :=
        ⟨(⟨0, hn⟩, σ (Fin.last 1) ⟨0, hn⟩), mem_matSupport_permMatrix_self _ _⟩
      have hc : ∀ S ∈ φ.powerset.filter (·.Nonempty),
          (closedPoly n (B \ S)).eval 0 = 1 := by
        intro S hS
        exact closedPoly_eval_zero ((hchild S hS).hasPerm (by omega))
      have hsum : (∑ S ∈ φ.powerset.filter (·.Nonempty),
          (-1 : ℚ) ^ (S.card + 1) * (closedPoly n (B \ S)).eval 0) = 1 := by
        calc
          _ = ∑ S ∈ φ.powerset.filter (·.Nonempty), (-1 : ℚ) ^ (S.card + 1) := by
            apply Finset.sum_congr rfl
            intro S hS
            rw [hc S hS, mul_one]
          _ = 1 := sum_nonempty_subsets_sign φ hφ
      norm_num only [Nat.cast_zero, Nat.cast_one, neg_zero, zero_add] at hrec ⊢
      rw [closedPoly_eval_zero hB, hsum] at hrec
      linarith
    · have hkpos : 1 ≤ k := by omega
      have hprev := ih hkpos B
        ((show HasDisjointPerms n B (k + 1 + 1) from ⟨σ, hσ, hd⟩).mono_count (by omega))
      have hsum : (∑ S ∈ φ.powerset.filter (·.Nonempty),
          (-1 : ℚ) ^ (S.card + 1) * (closedPoly n (B \ S)).eval (-(k : ℚ))) = 0 := by
        apply Finset.sum_eq_zero
        intro S hS
        rw [ih hkpos (B \ S) (hchild S hS), mul_zero]
      rw [hprev, hsum] at hrec
      linarith

theorem hasDisjointPerms_univ (n : ℕ) (hn : 1 ≤ n) :
    HasDisjointPerms n Finset.univ n := by
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨σ, hd⟩ := exists_cyclic_perms_pairwise_disjoint n
  exact ⟨σ, fun _ => Finset.subset_univ _, hd⟩

/-- The full negative-integer vanishing milestone, for any polynomial representing
the semi-magic counting function. -/
theorem semiMagic_polynomial_vanishing (n : ℕ) (hn : 1 ≤ n) (P : Polynomial ℚ)
    (hP : ∀ t : ℕ, P.eval (t : ℚ) = (MagicSquares.semiMagicCount n t : ℚ)) :
    ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) - 1 → P.eval (-(k : ℚ)) = 0 := by
  have hgood : HasPerm n Finset.univ := ⟨Equiv.refl _, Finset.subset_univ _⟩
  have heq : P = closedPoly n Finset.univ := by
    apply sub_eq_zero.mp
    apply poly_eq_zero_of_nat_eval_eq_zero
    intro t
    rw [Polynomial.eval_sub, hP t, closedPoly_eval_of_hasPerm hgood t,
      card_closedFiber_univ, sub_self]
  intro k hk hkn
  lift k to ℕ using (by omega)
  have hkpos : 1 ≤ k := by omega
  have hkn' : k + 1 ≤ n := by omega
  rw [heq]
  exact_mod_cast closedPoly_neg_eq_zero_of_disjointPerms n hn k hkpos Finset.univ
    ((hasDisjointPerms_univ n hn).mono_count hkn')

end MagicSquaresSpencer
