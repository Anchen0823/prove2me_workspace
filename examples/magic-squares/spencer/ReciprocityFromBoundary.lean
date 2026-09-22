import examples.«magic-squares».spencer.FiniteBoundaryBalance
import examples.«magic-squares».spencer.ReflectionSign
import examples.«magic-squares».spencer.ReflectionExtension
import examples.«magic-squares».spencer.ClosedVanishing

set_option autoImplicit false

namespace MagicSquaresSpencer
open Polynomial MagicSquares

/-- A finite boundary Euler identity suffices for the full reciprocity milestone.
The hypothesis remains unproved; no Ehrhart reciprocity theorem is imported. -/
theorem semiMagic_reciprocity_of_finiteBoundaryEuler (n : ℕ) (hn : 1 ≤ n)
    (p : Polynomial ℚ)
    (hp : ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ))
    (he : FiniteBoundaryEuler n) :
    ∀ t : ℤ, p.eval (((-(n : ℤ) - t : ℤ) : ℚ)) =
      (-1 : ℚ) ^ (n - 1) * p.eval (t : ℚ) := by
  have href := semiMagic_normalized_reflection_of_boundaryBalance n hn p hp
    (finiteBoundaryEuler_implies_boundaryBalance n he)
  have hne : p ≠ 0 := by
    intro hz
    have h0 := hp 0
    norm_num [hz, semiMagicCount_zero] at h0
  have hsign := reflection_sign p hne n
    (sB n (Finset.univ : Finset (Fin n × Fin n))) href
  obtain ⟨q, hdeg, hq⟩ := exists_polynomial_semiMagicCount_all_degree_eq n hn
  have heq : q = p := by
    apply sub_eq_zero.mp
    apply poly_eq_zero_of_nat_eval_eq_zero
    intro t
    rw [Polynomial.eval_sub, hq, hp, sub_self]
  rw [heq] at hdeg
  rw [hdeg, neg_one_pow_sub_sq] at hsign
  intro t
  have hx := href (t : ℚ)
  rw [hsign] at hx
  simpa only [Int.cast_sub, Int.cast_neg, Int.cast_natCast] using hx

/-- A conditional proof of the entire mission root, with one explicit finite
combinatorial hypothesis. This is a reduction, not a proof of that hypothesis. -/
theorem semiMagic_root_of_finiteBoundaryEuler (n : ℕ) (hn : 1 ≤ n)
    (he : FiniteBoundaryEuler n) :
    ∃ p : Polynomial ℚ,
      p.natDegree = (n - 1) ^ 2 ∧
        (∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)) ∧
          (∀ t : ℤ, p.eval (((-(n : ℤ) - t : ℤ) : ℚ)) =
            (-1 : ℚ) ^ (n - 1) * p.eval (t : ℚ)) ∧
          (∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) - 1 → p.eval (-(k : ℚ)) = 0) := by
  obtain ⟨p, hdeg, hp⟩ := exists_polynomial_semiMagicCount_all_degree_eq n hn
  exact ⟨p, hdeg, hp, semiMagic_reciprocity_of_finiteBoundaryEuler n hn p hp he,
    semiMagic_polynomial_vanishing n hn p hp⟩

end MagicSquaresSpencer
