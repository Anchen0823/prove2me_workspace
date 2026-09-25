/-
Prototype for Mission V's goal statement shape (BCCG Theorem 1, Ehrhart--Stanley).

Purpose of this file: settle the open questions in
`missions/magic-squares-v/DESIGN.md` §3 *before* drafting the proposal.

Findings (2026-09-19):

  * `∃ p : Polynomial ℚ, …` over `semiMagicCount n t` elaborates fine.
  * **`Polynomial.eval₂` does NOT work for negative arguments**: it wants a ring
    hom `R →+* S` with `p : R[X]`, and there is no ring hom `ℚ →+* ℤ`.  The two
    encodings that do work are
      (a) `∀ t : ℤ, p.eval (((-(n:ℤ) - t : ℤ) : ℚ)) = (-1:ℚ)^(n-1) * p.eval ((t:ℤ):ℚ)`
          — cast the integer to `ℚ` first, then `Polynomial.eval`;
      (b) the polynomial identity `p.comp (C (-(n:ℚ)) - X) = C ((-1:ℚ)^(n-1)) * p`.
    Both compile; (a) is the readable one and reads exactly like BCCG's display.
  * `p.natDegree = (n - 1) ^ 2` is the right encoding, with the `n = 1` corner
    covered by `Polynomial.natDegree_X_add_C`-style facts.
-/
import Mathlib
import Definitions.Def_MagicSquares

set_option autoImplicit false

open MagicSquares

namespace MagicSquaresVPrototype

/-- Shape 1: existence of the Ehrhart polynomial, with the right degree. -/
theorem semi_magic_polynomial_shape (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : Polynomial ℚ,
      p.natDegree = (n - 1) ^ 2 ∧
        (∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)) := by
  sorry

/-- Shape 2a: reciprocity at integer arguments, cast into `ℚ` first. -/
theorem semi_magic_reciprocity_shape (n : ℕ) (hn : 1 ≤ n) (p : Polynomial ℚ)
    (hp : ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)) :
    ∀ t : ℤ, p.eval (((-(n : ℤ) - t : ℤ) : ℚ))
      = (-1 : ℚ) ^ (n - 1) * p.eval ((t : ℤ) : ℚ) := by
  sorry

/-- Shape 2b: the same reciprocity as a polynomial identity. -/
theorem semi_magic_reciprocity_shape_as_poly (n : ℕ) (hn : 1 ≤ n) (p : Polynomial ℚ)
    (hp : ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)) :
    p.comp (Polynomial.C (-(n : ℚ)) - Polynomial.X)
      = Polynomial.C ((-1 : ℚ) ^ (n - 1)) * p := by
  sorry

/-- Shape 3: the vanishing list `H_n(-1) = … = H_n(-n+1) = 0`. -/
theorem semi_magic_vanishing_shape (n : ℕ) (hn : 1 ≤ n) (p : Polynomial ℚ)
    (hp : ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)) :
    ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) - 1 → p.eval (-(k : ℚ)) = 0 := by
  sorry

/-- Shape 4 (the packaged goal): the whole of BCCG Theorem 1 in one statement —
this is the shape for the mission's `main_item_id`. -/
theorem semi_magic_polynomial (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : Polynomial ℚ,
      p.natDegree = (n - 1) ^ 2 ∧
        (∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)) ∧
          (∀ t : ℤ, p.eval (((-(n : ℤ) - t : ℤ) : ℚ))
            = (-1 : ℚ) ^ (n - 1) * p.eval ((t : ℤ) : ℚ)) ∧
            (∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) - 1 → p.eval (-(k : ℚ)) = 0) := by
  sorry

/-! ## Non-vacuity checks

Each shape must be satisfiable by a concrete polynomial.  For `n = 2` we have
`H_2(t) = t + 1`, so `p = X + 1` should witness everything. -/

/-- `X + 1` has degree 1, which is `(2-1)^2`. -/
example : (Polynomial.X + 1 : Polynomial ℚ).natDegree = ((2 : ℕ) - 1) ^ 2 := by
  rw [show ((2 : ℕ) - 1) ^ 2 = 1 from by norm_num]
  change (Polynomial.X + Polynomial.C (1 : ℚ)).natDegree = 1
  rw [Polynomial.natDegree_X_add_C]

/-- `X + 1` evaluates to `H_2(t) = t + 1` on the nonnegative integers. -/
example (t : ℕ) : (Polynomial.X + 1 : Polynomial ℚ).eval (t : ℚ) = ((t + 1 : ℕ) : ℚ) := by
  simp [Polynomial.eval_add, Polynomial.eval_X]

/-- Reciprocity as encoded in shape 2a: for `n = 2`, `p(-2 - t) = -p(t)`. -/
example (t : ℤ) :
    (Polynomial.X + 1 : Polynomial ℚ).eval (((-(2 : ℤ) - t : ℤ) : ℚ)) =
      (-1 : ℚ) ^ ((2 : ℕ) - 1) * (Polynomial.X + 1 : Polynomial ℚ).eval ((t : ℤ) : ℚ) := by
  simp [Polynomial.eval_add, Polynomial.eval_X]
  ring

/-- For `n = 2` the vanishing list is the single point `k = 1`, i.e. the condition
is `p(-1) = 0`.  `X + 1` satisfies it, so the encoded shape is consistent with
`H_2(-1) = 0` (which reciprocity also forces). -/
example (k : ℤ) (h1 : 1 ≤ k) (h2 : k ≤ (2 : ℤ) - 1) :
    (Polynomial.X + 1 : Polynomial ℚ).eval (-(k : ℚ)) = 0 := by
  have hk : k = 1 := by omega
  subst hk
  norm_num

/-! ### The vanishing list for `n = 3`, checked on MacMahon's polynomial

`H_3(t) = 3 * C(t+3,4) + C(t+2,2)`, i.e. as a polynomial
`3 * (t+3)(t+2)(t+1)t/24 + (t+2)(t+1)/2`.  BCCG's vanishing list says it must
vanish at `t = -1` and `t = -2`. -/

/-- MacMahon's `H_3` polynomial, as a function `ℚ → ℚ`. -/
def h3poly (t : ℚ) : ℚ := 3 * ((t + 3) * (t + 2) * (t + 1) * t / 24) + (t + 2) * (t + 1) / 2

/-- `H_3(-1) = 0`. -/
example : h3poly (-1) = 0 := by norm_num [h3poly]

/-- `H_3(-2) = 0`. -/
example : h3poly (-2) = 0 := by norm_num [h3poly]

/-- Sanity on the positive side: `H_3(0..4) = 1, 6, 21, 55, 120`. -/
example : (h3poly 0, h3poly 1, h3poly 2, h3poly 3, h3poly 4)
    = (1, 6, 21, 55, 120) := by
  norm_num [h3poly]

end MagicSquaresVPrototype
