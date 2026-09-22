import examples.«magic-squares».spencer.SupportConstants
import examples.«magic-squares».spencer.PositiveTranslation

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace MagicSquaresSpencer

open Finset Polynomial MagicSquares
attribute [local instance] Classical.propDecidable

/-- The exact-full-support polynomial at line sum `x+n` is the ordinary
semi-magic counting polynomial at `x`. -/
theorem fullSupport_poly_shift (n : ℕ) (hn : 1 ≤ n) (p : Polynomial ℚ)
    (hp : ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)) :
    ((qB n (Finset.univ : Finset (Fin n × Fin n))).comp (X - 1)).comp
      (X + C (n : ℚ)) = p := by
  apply sub_eq_zero.mp
  apply poly_eq_zero_of_nat_eval_eq_zero
  intro t
  simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_C]
  have hshift : (t : ℚ) + (n : ℚ) - 1 = ((t + n - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ t + n)]
    push_cast
    ring
  rw [hshift, qB_eval]
  have hnat : t + n - 1 + 1 = t + n := by omega
  simp only [gB, hnat]
  rw [card_fullSupport_fiber_shift n t, hp t, sub_self]

/-- The first negative argument beyond the standard vanishing list is the
constant of the exact-full-support polynomial. -/
theorem sB_univ_eq_eval_neg_n (n : ℕ) (hn : 1 ≤ n) (p : Polynomial ℚ)
    (hp : ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)) :
    sB n (Finset.univ : Finset (Fin n × Fin n)) = p.eval (-(n : ℚ)) := by
  have h := congrArg (fun P : Polynomial ℚ => P.eval (-(n : ℚ)))
    (fullSupport_poly_shift n hn p hp)
  simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C, neg_add_cancel, Polynomial.eval_sub, Polynomial.eval_one,
    zero_sub, sB] at h
  exact h

/-- A finite Boolean alternating sum for the first non-vanishing candidate
`p(-n)`. No Euler-characteristic or reciprocity assertion is used. -/
theorem eval_neg_n_eq_alternating_hasPerm (n : ℕ) (hn : 1 ≤ n)
    (p : Polynomial ℚ)
    (hp : ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)) :
    p.eval (-(n : ℚ)) =
      ∑ S ∈ (Finset.univ : Finset (Fin n × Fin n)).powerset,
        (-1 : ℚ) ^ S.card *
          (if HasPerm n ((Finset.univ : Finset (Fin n × Fin n)) \ S) then 1 else 0) := by
  rw [← sB_univ_eq_eval_neg_n n hn p hp,
    sB_eq_alternating_hasPerm]

end MagicSquaresSpencer
