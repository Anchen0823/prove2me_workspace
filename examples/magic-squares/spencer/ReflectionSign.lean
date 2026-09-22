import Mathlib

set_option autoImplicit false

open Polynomial

theorem reflection_sign
    (p : Polynomial ℚ) (hp : p ≠ 0) (n : ℕ) (c : ℚ)
    (h : ∀ x : ℚ, p.eval (-(n : ℚ) - x) = c * p.eval x) :
    c = (-1 : ℚ) ^ p.natDegree := by
  let q : Polynomial ℚ := -(X + C (n : ℚ))
  have hq_nat : q.natDegree ≠ 0 := by
    dsimp only [q]
    rw [Polynomial.natDegree_neg, Polynomial.natDegree_X_add_C]
    norm_num
  have hpoly : p.comp q = C c * p := by
    apply Polynomial.funext
    intro x
    simp only [q, Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_mul]
    rw [show -(x + (n : ℚ)) = -(n : ℚ) - x by ring]
    exact h x
  have hlc := congrArg Polynomial.leadingCoeff hpoly
  have hcp : c ≠ 0 := by
    intro hc
    have hz : p.comp q = 0 := by simpa [hc] using hpoly
    have hz' := (Polynomial.comp_eq_zero_iff.mp hz)
    rcases hz' with hp0 | hq0
    · exact hp hp0
    · have : q.natDegree = 0 := by rw [hq0.2]; simp
      exact hq_nat this
  rw [Polynomial.leadingCoeff_comp hq_nat] at hlc
  rw [Polynomial.leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hcp)] at hlc
  have hp_lc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have hq_lc : q.leadingCoeff = (-1 : ℚ) := by
    change (-(X + C (n : ℚ))).leadingCoeff = (-1 : ℚ)
    rw [Polynomial.leadingCoeff_neg, Polynomial.leadingCoeff_X_add_C]
  rw [hq_lc] at hlc
  apply (mul_right_cancel₀ hp_lc)
  simpa [mul_comm, mul_left_comm, mul_assoc] using hlc.symm
