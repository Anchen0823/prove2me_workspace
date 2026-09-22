import examples.«magic-squares».spencer.S5
import examples.«magic-squares».spencer.Degree

/-!
# Bridge from rung S5 to the exact-degree mission statement

`S5.lean` identifies agreement at `t = 0` with the numerical identity
`sum B in supportSet n, sB n B = 1`.  `Degree.lean` independently supplies the unique counting
polynomial on the positive integers with exact degree `(n - 1) ^ 2`.  This file joins the two
statements by polynomial uniqueness.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset

namespace MagicSquaresSpencer

open Polynomial
open MagicSquares

/-- The numerical S5 identity is equivalent to polynomiality of `semiMagicCount n` on all
natural line sums.  No degree hypothesis is needed in either direction. -/
theorem sum_sB_eq_one_iff_exists_polynomial_semiMagicCount (n : ℕ) :
    (∑ B ∈ supportSet n, sB n B = 1) ↔
      ∃ p : Polynomial ℚ, ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ) := by
  constructor
  · exact exists_polynomial_semiMagicCount_of_sum_sB n
  · rintro ⟨p, hp⟩
    have hpq : p = qAll n := by
      have hzero : p - qAll n = 0 :=
        poly_eq_zero_of_pos_eval_eq_zero fun t ht => by
          rw [Polynomial.eval_sub, hp t, qAll_eval_pos ht, sub_self]
      exact sub_eq_zero.mp hzero
    calc
      ∑ B ∈ supportSet n, sB n B = (qAll n).eval ((0 : ℕ) : ℚ) :=
        (qAll_eval_zero n).symm
      _ = p.eval ((0 : ℕ) : ℚ) := by rw [hpq]
      _ = (semiMagicCount n 0 : ℚ) := hp 0
      _ = 1 := by rw [semiMagicCount_zero, Nat.cast_one]

/-- The exact-degree, all-natural-number form of Spencer's theorem, conditional only on the
numerical S5 identity.  This has the shape of the Magic Squares V mission goal. -/
theorem exists_polynomial_semiMagicCount_degree_eq_of_sum_sB (n : ℕ) (hn : 1 ≤ n)
    (h : ∑ B ∈ supportSet n, sB n B = 1) :
    ∃ p : Polynomial ℚ, p.natDegree = (n - 1) ^ 2 ∧
      ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ) := by
  obtain ⟨p, hpdeg, hpval⟩ := exists_polynomial_semiMagicCount_degree_eq n hn
  have hpq : p = qAll n := by
    have hzero : p - qAll n = 0 :=
      poly_eq_zero_of_pos_eval_eq_zero fun t ht => by
        rw [Polynomial.eval_sub, hpval t ht, qAll_eval_pos ht, sub_self]
    exact sub_eq_zero.mp hzero
  refine ⟨p, hpdeg, fun t => ?_⟩
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [hpq, qAll_eval_zero, h, semiMagicCount_zero, Nat.cast_one]
  · exact hpval t ht

end MagicSquaresSpencer
