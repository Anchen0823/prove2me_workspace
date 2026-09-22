import Mathlib
import examples.«magic-squares».spencer.S5

set_option autoImplicit false

namespace MagicSquaresSpencer

open Polynomial

/-- A reflection identity known on all natural arguments extends to every rational
argument by polynomial uniqueness. -/
theorem polynomial_reflection_extension (p : Polynomial ℚ) (n : ℕ) (s : ℚ)
    (h : ∀ t : ℕ, p.eval (-((n : ℚ)) - (t : ℚ)) = s * p.eval (t : ℚ)) :
    ∀ x : ℚ, p.eval (-((n : ℚ)) - x) = s * p.eval x := by
  let r : Polynomial ℚ := p.comp (C (-((n : ℚ))) - X) - C s * p
  have hr : r = 0 := by
    apply poly_eq_zero_of_nat_eval_eq_zero
    intro t
    simp only [r, eval_sub, eval_comp, eval_sub, eval_C, eval_X, eval_mul]
    rw [h t]
    ring
  intro x
  have hx := congrArg (fun q : Polynomial ℚ => q.eval x) hr
  simp only [r, eval_sub, eval_comp, eval_sub, eval_C, eval_X, eval_mul,
    eval_zero] at hx
  linarith

/-- The sign contributed by the square of `n - 1` is the same as that contributed
by `n - 1`. -/
theorem neg_one_pow_sub_sq (n : ℕ) :
    (-1 : ℚ) ^ ((n - 1) ^ 2) = (-1 : ℚ) ^ (n - 1) := by
  rw [neg_one_pow_eq_pow_mod_two (R := ℚ),
    neg_one_pow_eq_pow_mod_two (R := ℚ)]
  let m := (n - 1) % 2
  have hm : m < 2 := by
    dsimp [m]
    exact Nat.mod_lt _ (by decide)
  have hsq : m ^ 2 % 2 = m := by
    interval_cases m <;> norm_num
  have he : ((n - 1) % 2 % 2) ^ 2 % 2 = (n - 1) % 2 := by
    simpa [m] using hsq
  have he' : (n - 1) ^ 2 % 2 % 2 = (n - 1) % 2 := by
    simpa [Nat.pow_mod] using he
  rw [he']
  exact (neg_one_pow_eq_pow_mod_two (R := ℚ) (n - 1)).symm

end MagicSquaresSpencer
