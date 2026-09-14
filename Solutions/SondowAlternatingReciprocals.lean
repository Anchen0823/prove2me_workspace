import Solutions.SondowBinomialCoefficients
import Mathlib.NumberTheory.Harmonic.Defs

open Finset

namespace EulerMascheroni.Sondow

theorem alternating_choose_div_succ (n : ℕ) :
    (∑ j ∈ range (n+1), (-1:ℝ)^j*(n.choose j:ℝ)/(j+1:ℕ)) = 1/(n+1:ℕ) := by
  have halt := signed_choose_sum (n+1) (by omega)
  rw [sum_range_succ'] at halt
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul] at halt
  have he (j : ℕ) : (-1:ℝ)^j*(n.choose j:ℝ)/(j+1:ℕ) =
      -((-1:ℝ)^(j+1)*((n+1).choose (j+1):ℝ))/(n+1:ℕ) := by
    have hc : (n+1:ℕ)*(n.choose j:ℝ) = ((n+1).choose (j+1):ℝ)*(j+1:ℕ) := by
      exact_mod_cast Nat.add_one_mul_choose_eq n j
    have hn0 : (n+1:ℕ) ≠ (0:ℝ) := by positivity
    have hj0 : (j+1:ℕ) ≠ (0:ℝ) := by positivity
    rw [pow_succ]
    field_simp
    nlinarith [congrArg (fun z : ℝ => (-1:ℝ)^j*z) hc]
  simp_rw [he, ← sum_div, sum_neg_distrib]
  congr 1
  linarith

/-- Pascal recurrence as a finite difference operator on a test sequence. -/
theorem alternating_choose_pascal (n : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ range (n+2), (-1:ℝ)^j*((n+1).choose j:ℝ)*f j) =
      (∑ j ∈ range (n+1), (-1:ℝ)^j*(n.choose j:ℝ)*f j) -
        ∑ j ∈ range (n+1), (-1:ℝ)^j*(n.choose j:ℝ)*f (j+1) := by
  have htail := sum_range_succ' (fun j => (-1:ℝ)^j*(n.choose j:ℝ)*f j) (n+1)
  rw [sum_range_succ] at htail
  simp only [Nat.choose_succ_self, Nat.cast_zero, mul_zero, zero_mul, add_zero,
    pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul] at htail
  have he (j : ℕ) : (-1:ℝ)^(j+1)*((n+1).choose (j+1):ℝ)*f (j+1) =
      -((-1:ℝ)^j*(n.choose j:ℝ)*f (j+1)) +
        (-1:ℝ)^(j+1)*(n.choose (j+1):ℝ)*f (j+1) := by
    rw [Nat.choose_succ_succ', Nat.cast_add, pow_succ]
    ring
  rw [show n+2 = (n+1)+1 by omega, sum_range_succ']
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul]
  simp_rw [he, sum_add_distrib, sum_neg_distrib]
  linarith

theorem alternating_choose_div_index (n : ℕ) :
    (∑ j ∈ range (n+1), (-1:ℝ)^j*(n.choose j:ℝ)/(j:ℝ)) = -(harmonic n:ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he := alternating_choose_pascal n (fun j => (j:ℝ)⁻¹)
    simp only [← div_eq_mul_inv] at he
    rw [he, ih, alternating_choose_div_succ, harmonic_succ]
    push_cast
    ring

end EulerMascheroni.Sondow

#print axioms EulerMascheroni.Sondow.alternating_choose_div_succ
#print axioms EulerMascheroni.Sondow.alternating_choose_pascal
#print axioms EulerMascheroni.Sondow.alternating_choose_div_index
