/-
# Brick 8: summing the support fibres back up — the bridge to the platform's `semiMagicCount`

`Recursion.lean` proves that each support contributes a polynomial in the line sum (`isPolyDegLe_gB`).
What is still missing to say anything about the platform's `H_n(t) = semiMagicCount n t` is that the
support fibres *partition* the semi-magic squares.  That is this file (rung **S4a**), together with
the shift that turns "polynomial in `r` at line sum `r + 1`" into "polynomial in `t` at line sum
`t`" (rung **S4b**).

Two things to keep in mind, both from `SPENCER-ROUTE.md`:

* the platform's `semiMagicSquares n t` is a *filter of `Finset.univ`* on `Square n (Fin (t+1))`,
  while `matBox n t` is the image of that same `univ` under the entry coercion `Fin (t+1) → ℕ`.
  The bridge is a bijection along the coercion (and the coercion is injective);
* the conclusion is the **`t ≥ 1`** statement.  Agreement at `t = 0` is *not* claimed — it is the
  reciprocity content (rung S5, §4.1 of the route notes) — and the degree bound here is `n ^ 2`,
  not the sharp `(n-1) ^ 2` (that is rung S3, the face-rank count).

Scratch file, built with `lake build examples.«magic-squares».spencer.Aggregate`.
-/
import Mathlib
import Definitions.Def_MagicSquares
import examples.«magic-squares».spencer.Recursion

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset

namespace MagicSquaresSpencer

open Polynomial
open MagicSquares

variable {n : ℕ}

/-! ## S4a: the fibres partition the semi-magic squares -/

/-- The platform's `IsSemiMagic` is verbatim the row-and-column condition that `LineSums` names:
`rowSum`/`colSum` are the very same `∑ j`/`∑ i`. -/
theorem isSemiMagic_iff_lineSums {n t : ℕ} (M : Matrix (Fin n) (Fin n) ℕ) :
    IsSemiMagic M t ↔ LineSums M t :=
  ⟨fun h => h, fun h => h⟩

/-- The line-sum-`t` part of the box, as a *named* finset.  This has to be a def rather than a
literal `Finset.filter` in a statement: a raw `filter` in a theorem's *type* needs a
`DecidablePred` instance, and the `classical` inside the proof body cannot supply one (the
statement is elaborated first).  `matFiber` and the platform's own `semiMagicSquares` are written
the same way, for the same reason. -/
noncomputable def matBoxLine (n t : ℕ) : Finset (Matrix (Fin n) (Fin n) ℕ) := by
  classical
  exact (matBox n t).filter fun M => LineSums M t

/-- **The bridge, at the level of the box.**  `matBox n t` is `Finset.univ` transported along the
entry coercion, so counting the line-sum-`t` members of the box is the same as counting the
platform's semi-magic squares of line sum `t`. -/
theorem card_matBoxLine (n t : ℕ) : (matBoxLine n t).card = semiMagicCount n t := by
  classical
  have hset : (Finset.univ.filter fun M : Square n (Fin (t + 1)) =>
        LineSums (fun i j => (M i j : ℕ)) t) = semiMagicSquares n t := by
    rw [semiMagicSquares]
    exact Finset.filter_congr fun M _ => (isSemiMagic_iff_lineSums _).symm
  rw [matBoxLine, semiMagicCount, ← hset, matBox, Finset.filter_map, Finset.card_map]
  refine congrArg Finset.card (Finset.filter_congr fun M _ => ?_)
  exact ⟨fun h => h, fun h => h⟩

/-- The fibre over `B` is exactly the `matSupport`-fibre of the line-sum-`t` part of the box. -/
theorem matFiber_eq_filter_matBoxLine {n t : ℕ} (B : Finset (Fin n × Fin n)) :
    matFiber n t t B = (matBoxLine n t).filter (fun M => matSupport M = B) := by
  classical
  rw [matBoxLine, matFiber, Finset.filter_filter]

/-- **The fibres sum to the count.**  Every semi-magic square has exactly one support, so the fibres
`matFiber n t t B` (over all supports `B`, i.e. over the whole powerset — the non-supports
contribute nothing) partition the set counted by `semiMagicCount`. -/
theorem semiMagicCount_eq_sum_matFiber (n t : ℕ) :
    semiMagicCount n t
      = ∑ B ∈ (Finset.univ : Finset (Fin n × Fin n)).powerset, (matFiber n t t B).card := by
  classical
  rw [← card_matBoxLine n t]
  rw [Finset.card_eq_sum_card_fiberwise (f := matSupport) (s := matBoxLine n t)
    (t := (Finset.univ : Finset (Fin n × Fin n)).powerset)
    (fun M _ => Finset.mem_powerset.mpr (Finset.subset_univ _))]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [matFiber_eq_filter_matBoxLine B]

/-! ## S4b: shifting down by one, and the aggregate -/

/-- **Shifting a polynomial sequence down.**  If `b` agrees with a polynomial of degree `≤ K`, so
does `t ↦ b (t - 1)` — for `t ≥ 1`, by substituting `X - 1` (the identity `↑(t-1) = ↑t - 1` is what
fails at `t = 0`, and nothing is claimed there). -/
theorem exists_poly_comp_X_sub_one {K : ℕ} {b : ℕ → ℚ} (h : IsPolyDegLe K b) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ K ∧ ∀ t : ℕ, 1 ≤ t → p.eval (t : ℚ) = b (t - 1) := by
  obtain ⟨P, hPdeg, hPval⟩ := h
  refine ⟨P.comp (Polynomial.X - Polynomial.C 1), ?_, fun t ht => ?_⟩
  · refine (Polynomial.natDegree_comp_le (p := P) (q := Polynomial.X - Polynomial.C 1)).trans ?_
    have hq : (Polynomial.X - Polynomial.C (1 : ℚ)).natDegree ≤ 1 := by
      calc (Polynomial.X - Polynomial.C (1 : ℚ)).natDegree
          ≤ max (Polynomial.X : ℚ[X]).natDegree (Polynomial.C (1 : ℚ)).natDegree :=
            Polynomial.natDegree_sub_le _ _
        _ ≤ max 1 0 := max_le_max (le_of_eq Polynomial.natDegree_X)
            (le_of_eq (Polynomial.natDegree_C (1 : ℚ)))
        _ = 1 := by norm_num
    calc P.natDegree * (Polynomial.X - Polynomial.C (1 : ℚ)).natDegree
        ≤ P.natDegree * 1 := Nat.mul_le_mul_left _ hq
      _ = P.natDegree := Nat.mul_one _
      _ ≤ K := hPdeg
  · have hval : ((t : ℚ) - 1) = ((t - 1 : ℕ) : ℚ) := by
      rw [Nat.cast_sub ht, Nat.cast_one]
    rw [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, hval,
      hPval (t - 1)]

/-- **Spencer (1980), aggregated.**  For every `t ≥ 1` the number of `n × n` semi-magic squares of
line sum `t` is the value of one fixed polynomial of degree at most `n ^ 2`.

Both restrictions are deliberate and are *not* oversights:

* `t ≥ 1`: the support recursion only sees positive line sums, and `p(0) = 1` is the
  Ehrhart–Macdonald reciprocity statement at `-1` (rung S5);
* degree `n ^ 2` rather than `(n-1) ^ 2`: that is the crude count that the recursion bounds alone
  give; the sharp bound needs the face rank `ρ(B) = |B| - v(B) + c(B)` (rung S3). -/
theorem exists_polynomial_semiMagicCount_pos (n : ℕ) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ n * n ∧
      ∀ t : ℕ, 1 ≤ t → p.eval (t : ℚ) = (semiMagicCount n t : ℚ) := by
  classical
  have hcard : ∀ B ∈ (Finset.univ : Finset (Fin n × Fin n)).powerset, B.card ≤ n * n := by
    intro B hB
    calc B.card ≤ (Finset.univ : Finset (Fin n × Fin n)).card :=
          Finset.card_le_card (Finset.mem_powerset.mp hB)
      _ = n * n := by simp
  have hsum : IsPolyDegLe (n * n)
      (fun r => ∑ B ∈ (Finset.univ : Finset (Fin n × Fin n)).powerset, gB n B r) :=
    isPolyDegLe_sum _ fun B hB => isPolyDegLe_mono (isPolyDegLe_gB n B) (hcard B hB)
  obtain ⟨p, hpdeg, hpval⟩ := exists_poly_comp_X_sub_one hsum
  refine ⟨p, hpdeg, fun t ht => ?_⟩
  rw [hpval t ht, semiMagicCount_eq_sum_matFiber n t]
  push_cast
  refine Finset.sum_congr rfl fun B _ => ?_
  show ((matFiber n ((t - 1) + 1) ((t - 1) + 1) B).card : ℚ) = ((matFiber n t t B).card : ℚ)
  rw [Nat.sub_add_cancel ht]

end MagicSquaresSpencer
