import examples.«magic-squares».spencer.S5

set_option autoImplicit false

namespace MagicSquaresSpencer

open Polynomial

/-- A polynomial with period one and zero initial value vanishes identically. -/
theorem polynomial_eq_zero_of_periodic_eval {r : Polynomial ℚ}
    (hstep : ∀ x : ℚ, r.eval (x + 1) = r.eval x)
    (hzero : r.eval 0 = 0) : r = 0 := by
  have hnat : ∀ n : ℕ, r.eval (n : ℚ) = 0 := by
    intro n
    induction n with
    | zero => simpa using hzero
    | succ n ih =>
        have h := hstep (n : ℚ)
        norm_cast at h ⊢
        exact h.trans ih
  exact poly_eq_zero_of_nat_eval_eq_zero hnat

/-- Equal first differences and equal initial values determine rational polynomials. -/
theorem polynomial_eq_of_eq_difference {p q : Polynomial ℚ}
    (hstep : ∀ x : ℚ, p.eval (x + 1) - p.eval x =
      q.eval (x + 1) - q.eval x)
    (hzero : p.eval 0 = q.eval 0) : p = q := by
  have hperiod : ∀ x : ℚ, (p - q).eval (x + 1) = (p - q).eval x := by
    intro x
    simp only [Polynomial.eval_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mp (by simpa [sub_sub_sub_comm] using hstep x)
  have hinit : (p - q).eval 0 = 0 := by
    simp [hzero]
  have h := polynomial_eq_zero_of_periodic_eval hperiod hinit
  exact sub_eq_zero.mp h

end MagicSquaresSpencer
