/-
Mission V — draft theorem statements, exactly as they will be uploaded to the
proposal (minus the `sorry`, which the platform keeps).

Preamble used on the platform: `import Mathlib` + `import Definitions.Def_MagicSquares`
+ `open MagicSquares`.  Everything is inside `namespace MagicSquares` (the
programme shares one namespace across the magic-square missions).

Compile with `lake env lean` — the `sorry`s are intentional.
-/
import Mathlib
import Definitions.Def_MagicSquares

set_option autoImplicit false

open MagicSquares

namespace MagicSquares

/-- M1 — order one: a `1 × 1` array whose row (and column) sums to `t` is just `[t]`. -/
theorem semi_magic_count_one (t : ℕ) : semiMagicCount 1 t = 1 := by
  sorry

/-- M4 — order four: the Ehrhart polynomial of the Birkhoff polytope `B_4`, cleared of
denominators.  The common denominator of the coefficients is `11340 = 9! * 11 / 352`…
in any case `11340 * H_4(t)` is the displayed integer polynomial, whose leading
coefficient `11/11340` is `vol(B_4)` and whose normalised volume `9! * 11/11340` is
`352`. -/
theorem semi_magic_count_four (t : ℕ) :
    11340 * semiMagicCount 4 t
      = 11 * t ^ 9 + 198 * t ^ 8 + 1596 * t ^ 7 + 7560 * t ^ 6 + 23289 * t ^ 5
        + 48762 * t ^ 4 + 70234 * t ^ 3 + 68220 * t ^ 2 + 40950 * t + 11340 := by
  sorry

/-- M5 — the hard rung, isolated: a polynomial `p` of degree `(n-1)^2` agreeing with
`H_n` on the nonnegative integers. -/
theorem semi_magic_polynomial_exists (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : Polynomial ℚ,
      p.natDegree = (n - 1) ^ 2 ∧
        ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ) := by
  sorry

/-- M6 — Ehrhart–Macdonald reciprocity for `H_n`. -/
theorem semi_magic_reciprocity (n : ℕ) (hn : 1 ≤ n) (p : Polynomial ℚ)
    (hp : ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)) :
    ∀ t : ℤ, p.eval (((-(n : ℤ) - t : ℤ) : ℚ))
      = (-1 : ℚ) ^ (n - 1) * p.eval ((t : ℤ) : ℚ) := by
  sorry

/-- M7 — the vanishing list `H_n(-1) = … = H_n(-n+1) = 0`, i.e. `p` vanishes at the
*negative* integers `-1, …, -(n-1)`. -/
theorem semi_magic_vanishing (n : ℕ) (hn : 1 ≤ n) (p : Polynomial ℚ)
    (hp : ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)) :
    ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) - 1 → p.eval (-(k : ℚ)) = 0 := by
  sorry

/-- GOAL — BCCG Theorem 1 (Ehrhart 1973, Stanley 1973): for every order `n ≥ 1`,
`H_n` agrees on the nonnegative integers with a polynomial of degree exactly
`(n-1)^2`, which moreover satisfies the reciprocity identity and vanishes at
`-1, …, -(n-1)`. -/
theorem semi_magic_polynomial (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : Polynomial ℚ,
      p.natDegree = (n - 1) ^ 2 ∧
        (∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)) ∧
          (∀ t : ℤ, p.eval (((-(n : ℤ) - t : ℤ) : ℚ))
            = (-1 : ℚ) ^ (n - 1) * p.eval ((t : ℤ) : ℚ)) ∧
            (∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) - 1 → p.eval (-(k : ℚ)) = 0) := by
  sorry

end MagicSquares
