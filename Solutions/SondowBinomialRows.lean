import Solutions.SondowAlternatingReciprocals
import Mathlib.Algebra.BigOperators.Intervals

open Finset

namespace EulerMascheroni.Sondow

noncomputable def binomialRow (n k : ℕ) : ℝ :=
  ∑ j ∈ range (n+1), (-1:ℝ)^j*(n.choose j:ℝ)/((j:ℝ)-k)

theorem binomialRow_zero (n : ℕ) : binomialRow n 0 = -(harmonic n:ℝ) := by
  simpa [binomialRow] using alternating_choose_div_index n

theorem binomialRow_pascal (n k : ℕ) :
    binomialRow (n+1) (k+1) = binomialRow n (k+1) - binomialRow n k := by
  have he := alternating_choose_pascal n (fun j => ((j:ℝ)-(k+1:ℕ))⁻¹)
  simpa [binomialRow, div_eq_mul_inv] using he

theorem neg_one_pow_complement (n j : ℕ) (hj : j ≤ n) :
    (-1:ℝ)^(n-j) = (-1:ℝ)^n*(-1:ℝ)^j := by
  have hsq : (-1:ℝ)^j*(-1:ℝ)^j = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  conv_rhs => rw [← Nat.sub_add_cancel hj, pow_add]
  rw [mul_assoc, hsq, mul_one]

theorem binomialRow_self (n : ℕ) : binomialRow n n = (-1:ℝ)^n*(harmonic n:ℝ) := by
  unfold binomialRow
  rw [← sum_range_reflect]
  simp only [Nat.add_sub_cancel]
  have he (j : ℕ) (hj : j ∈ range (n+1)) :
      (-1:ℝ)^(n-j)*(n.choose (n-j):ℝ)/((n-j:ℕ)-n:ℝ) =
        -(-1:ℝ)^n*((-1:ℝ)^j*(n.choose j:ℝ)/(j:ℝ)) := by
    have hjn : j ≤ n := by simpa using mem_range.mp hj
    rw [Nat.choose_symm hjn, Nat.cast_sub hjn, neg_one_pow_complement n j hjn]
    ring
  rw [sum_congr rfl he, ← mul_sum, alternating_choose_div_index]
  ring

theorem binomial_row_formula_pascal (n k : ℕ) (hk : k < n) :
    (-1:ℝ)^(k+1)*(n.choose (k+1):ℝ)*
        ((harmonic (k+1):ℝ)-(harmonic (n-(k+1)):ℝ)) -
      (-1:ℝ)^k*(n.choose k:ℝ)*((harmonic k:ℝ)-(harmonic (n-k):ℝ)) =
    (-1:ℝ)^(k+1)*((n+1).choose (k+1):ℝ)*
      ((harmonic (k+1):ℝ)-(harmonic ((n+1)-(k+1)):ℝ)) := by
  have hc : (n.choose (k+1):ℝ)/(n-k:ℕ) = (n.choose k:ℝ)/(k+1:ℕ) := by
    have hnk : (n-k:ℕ) ≠ (0:ℝ) := by exact_mod_cast (Nat.sub_pos_of_lt hk).ne'
    apply (div_eq_div_iff hnk (by positivity)).mpr
    exact_mod_cast Nat.choose_succ_right_eq n k
  have hH : (harmonic (n-k):ℝ) = (harmonic (n-(k+1)):ℝ) + 1/(n-k:ℕ) := by
    have hi : n-k = n-(k+1)+1 := by omega
    conv_lhs => rw [hi, harmonic_succ]
    push_cast
    rw [hi]
    push_cast
    ring
  have hK : (harmonic (k+1):ℝ) = (harmonic k:ℝ)+1/(k+1:ℕ) := by
    rw [harmonic_succ]
    push_cast
    ring
  rw [Nat.choose_succ_succ', Nat.cast_add, Nat.add_sub_add_right, hH, hK, pow_succ]
  linear_combination -(-1:ℝ)^k * hc

/-- Finite row identity underlying Sondow's Appendix combinatorial formula. -/
theorem binomialRow_eq_harmonic (n k : ℕ) (hk : k ≤ n) :
    binomialRow n k = (-1:ℝ)^k*(n.choose k:ℝ)*
      ((harmonic k:ℝ)-(harmonic (n-k):ℝ)) := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst k
    simp [binomialRow_zero]
  | succ n ih =>
    by_cases hk0 : k = 0
    · subst k
      simp [binomialRow_zero]
    by_cases hkn : k = n+1
    · subst k
      simp [binomialRow_self]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hki : k+1 ≤ n := by omega
    rw [binomialRow_pascal, ih (k+1) hki, ih k (by omega)]
    exact binomial_row_formula_pascal n k (by omega)

end EulerMascheroni.Sondow

#print axioms EulerMascheroni.Sondow.binomialRow_pascal
#print axioms EulerMascheroni.Sondow.binomialRow_self
#print axioms EulerMascheroni.Sondow.binomialRow_eq_harmonic
