/-
# The Spencer (1980) machinery, part 1 of 2: from a triangular recurrence to a polynomial

Spencer's elementary proof that the number `H_n(t)` of `n × n` semi-magic squares of line sum
`t` is a polynomial in `t` has two analytic-looking ingredients that are in fact purely
discrete:

* the **discrete antiderivative**: `P ↦ (n ↦ ∑_{m<n} P m)` raises the degree by exactly one;
  Mathlib supplies Bernoulli-polynomial Faulhaber (`Polynomial.bernoulli_succ_eval`), so this is
  `(B_{d+1}(X) - B_{d+1}) / (d+1)` for the monomial `X ^ d`;
* the **Spencer step**: a strictly triangular system of recurrences with polynomial coefficients
  of degree `≤ K` produces a polynomial of degree `≤ K + 1`.

What is *not* here yet — and what the combinatorics still has to supply — is the support-set
poset, the Hall/Birkhoff–von Neumann choice of a permutation inside a support set, and the
degree count.  See `missions/magic-squares-v/SPENCER-ROUTE.md` for the plan and for the two
subtleties (the value at line sum `0`, and the exact degree bound) that this note records.

Scratch file, compiled with `lake env lean`.
-/

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 400000

open Finset

namespace MagicSquaresSpencer

open Polynomial


/-- The Bernoulli polynomial of index `n` has degree at most `n`. -/
theorem natDegree_bernoulli_le (n : ℕ) : (Polynomial.bernoulli n).natDegree ≤ n := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun i hi => ?_
  rw [Polynomial.coeff_bernoulli, if_neg (by omega)]

/-- Subtracting a constant never increases the degree. -/
theorem natDegree_sub_C_le (p : Polynomial ℚ) (c : ℚ) : (p - C c).natDegree ≤ p.natDegree := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
  rw [Polynomial.coeff_sub, Polynomial.coeff_C, if_neg (by omega), sub_zero]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt hN

/-- The Bernoulli antiderivative of the monomial `X ^ d`: a polynomial of degree at most
`d + 1` whose value at `n : ℕ` is `∑_{m < n} m ^ d`. -/
noncomputable def bernoulliAntideriv (d : ℕ) : Polynomial ℚ :=
  C (((d : ℚ) + 1)⁻¹) * (Polynomial.bernoulli d.succ - C (_root_.bernoulli d.succ))

theorem bernoulliAntideriv_natDegree (d : ℕ) : (bernoulliAntideriv d).natDegree ≤ d + 1 := by
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  exact (natDegree_sub_C_le (Polynomial.bernoulli d.succ) _).trans
    ((natDegree_bernoulli_le d.succ).trans (by omega))

theorem bernoulliAntideriv_eval (d n : ℕ) :
    (bernoulliAntideriv d).eval (n : ℚ) = ∑ m ∈ range n, (m : ℚ) ^ d := by
  have h := Polynomial.bernoulli_succ_eval n d
  have hne : ((d : ℚ) + 1) ≠ 0 := by positivity
  simp only [bernoulliAntideriv, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub]
  rw [h]
  field_simp
  ring

/-- The antiderivative of a polynomial, built from the Bernoulli antiderivatives of its
monomials. -/
noncomputable def antideriv (P : Polynomial ℚ) : Polynomial ℚ :=
  ∑ p ∈ range (P.natDegree + 1), C (P.coeff p) * bernoulliAntideriv p

theorem antideriv_natDegree (P : Polynomial ℚ) : (antideriv P).natDegree ≤ P.natDegree + 1 := by
  refine Polynomial.natDegree_sum_le_of_forall_le (s := range (P.natDegree + 1))
    (fun p => C (P.coeff p) * bernoulliAntideriv p) fun p hp => ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  have hp' : p ≤ P.natDegree := by simpa using hp
  exact (bernoulliAntideriv_natDegree p).trans (by omega)

theorem antideriv_eval (P : Polynomial ℚ) (n : ℕ) :
    (antideriv P).eval (n : ℚ) = ∑ m ∈ range n, P.eval (m : ℚ) := by
  rw [antideriv, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  simp_rw [bernoulliAntideriv_eval]
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]

/-- **The discrete antiderivative.** For every polynomial `P` there is a polynomial `Q` of
degree at most `natDegree P + 1` with `Q n = ∑_{m < n} P m` for every `n : ℕ`. -/
theorem exists_antideriv (P : Polynomial ℚ) :
    ∃ Q : Polynomial ℚ, Q.natDegree ≤ P.natDegree + 1 ∧
      ∀ n : ℕ, Q.eval (n : ℚ) = ∑ m ∈ range n, P.eval (m : ℚ) :=
  ⟨antideriv P, antideriv_natDegree P, antideriv_eval P⟩



/-! ## Brick 2: the Spencer step, and its summing form -/

/-- `b` agrees with a polynomial of degree at most `K` on all of `ℕ`. -/
def IsPolyDegLe (K : ℕ) (b : ℕ → ℚ) : Prop :=
  ∃ p : Polynomial ℚ, p.natDegree ≤ K ∧ ∀ n : ℕ, p.eval (n : ℚ) = b n

theorem isPolyDegLe_const (c : ℚ) (K : ℕ) : IsPolyDegLe K (fun _ => c) :=
  ⟨C c, by simp, by intro n; simp⟩

/-- Degree bounds are inherited by weaker ones. -/
theorem isPolyDegLe_mono {K K' : ℕ} {b : ℕ → ℚ} (h : IsPolyDegLe K b) (hKK : K ≤ K') :
    IsPolyDegLe K' b := by
  obtain ⟨p, hp, hv⟩ := h
  exact ⟨p, hp.trans hKK, hv⟩

theorem isPolyDegLe_sum {ι : Type*} (s : Finset ι) {c : ι → ℕ → ℚ} {K : ℕ}
    (hc : ∀ i ∈ s, IsPolyDegLe K (c i)) :
    IsPolyDegLe K (fun n => ∑ i ∈ s, c i n) := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, by simp, by intro n; simp⟩
  | insert a s ha ih =>
      obtain ⟨p₁, hp₁, hv₁⟩ := hc a (Finset.mem_insert_self a s)
      obtain ⟨p₂, hp₂, hv₂⟩ := ih fun i hi => hc i (Finset.mem_insert_of_mem hi)
      refine ⟨p₁ + p₂, ?_, fun n => ?_⟩
      · exact (Polynomial.natDegree_add_le_iff_left p₁ p₂ hp₂).mpr hp₁
      · simp only [Polynomial.eval_add, hv₁ n, hv₂ n, Finset.sum_insert ha]

/-- **The Spencer step.** A sequence satisfying a triangular recurrence whose coefficients are
polynomial of degree at most `K` is itself polynomial of degree at most `K + 1`. -/
theorem isPolyDegLe_of_recurrence {b : ℕ → ℚ} {ι : Type*} (s : Finset ι) {c : ι → ℕ → ℚ} {K : ℕ}
    (hc : ∀ i ∈ s, IsPolyDegLe K (c i))
    (hrec : ∀ r : ℕ, 1 ≤ r → b r = b (r - 1) + ∑ i ∈ s, c i (r - 1)) :
    IsPolyDegLe (K + 1) b := by
  -- Step 1: telescoping.
  have htel : ∀ r : ℕ, b r = b 0 + ∑ t ∈ range r, ∑ i ∈ s, c i t := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
        rw [hrec (r + 1) (by omega), Nat.add_sub_cancel, ih, Finset.sum_range_succ]
        ring
  -- Step 2: the coefficient sequence, and its antiderivative.
  obtain ⟨R, hRdeg, hRval⟩ := isPolyDegLe_sum s hc
  obtain ⟨Q, hQdeg, hQval⟩ := exists_antideriv R
  have hC : (Polynomial.C (b 0)).natDegree ≤ K + 1 := by
    rw [Polynomial.natDegree_C]
    omega
  refine ⟨C (b 0) + Q, ?_, ?_⟩
  · exact (Polynomial.natDegree_add_le_iff_right (Polynomial.C (b 0)) Q hC).mpr
      (hQdeg.trans (by omega))
  · intro n
    rw [htel n, Polynomial.eval_add, Polynomial.eval_C, hQval n]
    congr 1
    exact Finset.sum_congr rfl fun t _ => hRval t

/-- The same step, in the *shifted* indexing that the fibre recurrence naturally produces.

The counting sequences of the support-set recursion are indexed so that the level-`(r+1)` count
satisfies `b (r+1) = b r + Σ …`; writing the recurrence with `r - 1` on the right costs a
case split that this form avoids.  Telescoping from `r = 0` is identical to the proof above. -/
theorem isPolyDegLe_of_recurrence_succ {b : ℕ → ℚ} {ι : Type*} (s : Finset ι) {c : ι → ℕ → ℚ}
    {K : ℕ} (hc : ∀ i ∈ s, IsPolyDegLe K (c i))
    (hrec : ∀ r : ℕ, b (r + 1) = b r + ∑ i ∈ s, c i r) :
    IsPolyDegLe (K + 1) b := by
  have htel : ∀ r : ℕ, b r = b 0 + ∑ t ∈ range r, ∑ i ∈ s, c i t := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
        rw [hrec r, ih, Finset.sum_range_succ]
        ring
  obtain ⟨R, hRdeg, hRval⟩ := isPolyDegLe_sum s hc
  obtain ⟨Q, hQdeg, hQval⟩ := exists_antideriv R
  have hC : (Polynomial.C (b 0)).natDegree ≤ K + 1 := by
    rw [Polynomial.natDegree_C]
    omega
  refine ⟨C (b 0) + Q, ?_, ?_⟩
  · exact (Polynomial.natDegree_add_le_iff_right (Polynomial.C (b 0)) Q hC).mpr
      (hQdeg.trans (by omega))
  · intro n
    rw [htel n, Polynomial.eval_add, Polynomial.eval_C, hQval n]
    congr 1
    exact Finset.sum_congr rfl fun t _ => hRval t



end MagicSquaresSpencer
