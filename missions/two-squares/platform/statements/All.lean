import Mathlib

namespace EqualTwoSquares

/-- Brahmagupta–Fibonacci identity, both forms. -/
theorem two_squares_mul {R : Type*} [CommRing R] (p q r s : R) :
    (p^2 + q^2) * (r^2 + s^2) = (p * r + q * s)^2 + (p * s - q * r)^2 ∧
      (p^2 + q^2) * (r^2 + s^2) = (p * r - q * s)^2 + (p * s + q * r)^2 := by sorry

/-- Objective 1: the four-parameter identity over the integers. -/
theorem four_param_identity (p q r s : ℤ) :
    (p * r + q * s)^2 + (p * s - q * r)^2 =
      (p * r - q * s)^2 + (p * s + q * r)^2 := by sorry

/-- Objective 2, equality part: the explicit one-parameter family, valid for every integer n. -/
theorem explicit_family_identity (n : ℤ) :
    (1 : ℤ)^2 + (n^2 - n + 1)^2 = (2 * n - 1)^2 + (n^2 - n - 1)^2 := by sorry

/-- Objective 2, inequality part: the four entries form a strict chain for every n at least 4. -/
theorem explicit_family_chain {n : ℤ} (hn : 4 ≤ n) :
    (1 : ℤ) < 2 * n - 1 ∧
      2 * n - 1 < n^2 - n - 1 ∧
        n^2 - n - 1 < n^2 - n + 1 := by sorry

/-- Objective 2 assembled: a positive solution with four pairwise distinct entries. -/
theorem explicit_family_solution {n : ℤ} (hn : 4 ≤ n) :
    (1 : ℤ)^2 + (n^2 - n + 1)^2 = (2 * n - 1)^2 + (n^2 - n - 1)^2 ∧
      (0 < (1 : ℤ) ∧ 0 < n^2 - n + 1 ∧ 0 < 2 * n - 1 ∧ 0 < n^2 - n - 1) ∧
        ((1 : ℤ) ≠ 2 * n - 1 ∧
          (1 : ℤ) ≠ n^2 - n - 1 ∧
            (1 : ℤ) ≠ n^2 - n + 1 ∧
              2 * n - 1 ≠ n^2 - n - 1 ∧
                2 * n - 1 ≠ n^2 - n + 1 ∧
                  n^2 - n - 1 ≠ n^2 - n + 1) := by sorry

/-- Objective 3: the parametrisation n ↦ (1, n^2-n+1, 2n-1, n^2-n-1) is injective. -/
theorem familyQuad_injective :
    Function.Injective
      (fun n : ℤ => ((1 : ℤ), n^2 - n + 1, 2 * n - 1, n^2 - n - 1)) := by sorry

/-- Objective 3: the family produces infinitely many distinct quadruples. -/
theorem family_patterns_infinite :
    (Set.range (fun n : ℤ => ((1 : ℤ), n^2 - n + 1, 2 * n - 1, n^2 - n - 1))).Infinite := by sorry

/-- Objective 3: no member of the family is a nontrivial integer multiple of another. -/
theorem family_scaling_trivial {m n k : ℤ}
    (h : ((1 : ℤ), n^2 - n + 1, 2 * n - 1, n^2 - n - 1) =
      k • ((1 : ℤ), m^2 - m + 1, 2 * m - 1, m^2 - m - 1)) :
    n = m := by sorry

/-- Every member of the family is primitive: the four entries have gcd one. -/
theorem family_primitive (n : ℤ) :
    Int.gcd (Int.gcd (1 : ℤ) (n^2 - n + 1)) (Int.gcd (2 * n - 1) (n^2 - n - 1)) = 1 := by sorry

/-- Objective 4, rearrangement: the sum-of-squares equation rewritten as a product equation. -/
theorem sum_sq_eq_iff_product (a b c d : ℤ) :
    a^2 + b^2 = c^2 + d^2 ↔ (a + c) * (a - c) = (d + b) * (d - b) := by sorry

/-- Objective 4, parity: after possibly swapping c and d, matching entries have equal parity. -/
theorem parity_alignment {a b c d : ℤ} (h : a^2 + b^2 = c^2 + d^2) :
    (Even (a - c) ∧ Even (b - d)) ∨ (Even (a - d) ∧ Even (b - c)) := by sorry

/-- Objective 4, substitution: under parity alignment the equation becomes XY = UV. -/
theorem sum_sq_eq_halves {a b c d : ℤ} (h : a^2 + b^2 = c^2 + d^2)
    (hac : Even (a - c)) (hbd : Even (b - d)) :
    ∃ X Y U V : ℤ,
      X + Y = a ∧ X - Y = c ∧ U - V = b ∧ U + V = d ∧ X * Y = U * V := by sorry

/-- Objective 5: every solution of XY = UV over the integers admits four parameters. -/
theorem four_factor_param (X Y U V : ℤ) (h : X * Y = U * V) :
    ∃ p q r s : ℤ, X = p * r ∧ Y = q * s ∧ U = p * s ∧ V = q * r := by sorry

/-- Objective 6, the goal: the four-parameter parametrisation is complete. -/
theorem complete_parametrization {a b c d : ℤ} (h : a^2 + b^2 = c^2 + d^2) :
    (∃ p q r s : ℤ,
      a = p * r + q * s ∧ b = p * s - q * r ∧
        c = p * r - q * s ∧ d = p * s + q * r) ∨
      (∃ p q r s : ℤ,
        a = p * r + q * s ∧ b = p * s - q * r ∧
          d = p * r - q * s ∧ c = p * s + q * r) := by sorry

end EqualTwoSquares
