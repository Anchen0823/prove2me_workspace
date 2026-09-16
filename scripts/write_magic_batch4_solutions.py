# -*- coding: utf-8 -*-
"""Write the six Solutions/ files for batch 4 and check them locally."""
import io
import os
import subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEANY = r"c:\Users\anche\.elan\toolchains\leanprover--lean4---v4.33.1\bin\lean.exe"

HEAD_BASE = """import Mathlib
import Definitions.Def_MagicSquares

set_option autoImplicit false

open MagicSquares
open scoped BigOperators
"""

HEAD_TRA = """import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresTransforms

set_option autoImplicit false

open MagicSquares
open scoped BigOperators
"""

# helpers used by the symmetry proofs (platform Def_MagicSquaresTransforms only
# carries the operations themselves)
HELPERS = """
/-! Auxiliary line-sum identities for the symmetry operations. The published
definition module provides only the operations, so the reindexing facts are
recorded here. -/

section helpers
variable {n : \u2115} {\u03b1 : Type*} [AddCommMonoid \u03b1]

private lemma rowSum_transpose' (M : Square n \u03b1) (i : Fin n) :
    rowSum (transpose M) i = colSum M i := by
  simp [rowSum, colSum, transpose]

private lemma colSum_transpose' (M : Square n \u03b1) (j : Fin n) :
    colSum (transpose M) j = rowSum M j := by
  simp [rowSum, colSum, transpose]

private lemma diagSum_transpose' (M : Square n \u03b1) :
    diagSum (transpose M) = diagSum M := by
  simp [diagSum, transpose]

private lemma antiDiagSum_transpose' (M : Square n \u03b1) :
    antiDiagSum (transpose M) = antiDiagSum M := by
  simp only [antiDiagSum, transpose]
  rw [\u2190 Function.Bijective.sum_comp Fin.rev_bijective (fun i => M (Fin.rev i) i)]
  simp

private lemma rowSum_flipVertical' (M : Square n \u03b1) (i : Fin n) :
    rowSum (flipVertical M) i = rowSum M (Fin.rev i) := by
  simp [rowSum, flipVertical]

private lemma colSum_flipVertical' (M : Square n \u03b1) (j : Fin n) :
    colSum (flipVertical M) j = colSum M j := by
  simp only [colSum, flipVertical]
  rw [\u2190 Function.Bijective.sum_comp Fin.rev_bijective (fun i => M i j)]

private lemma diagSum_flipVertical' (M : Square n \u03b1) :
    diagSum (flipVertical M) = antiDiagSum M := by
  simp only [diagSum, antiDiagSum, flipVertical]
  rw [\u2190 Function.Bijective.sum_comp Fin.rev_bijective (fun i => M i (Fin.rev i))]
  simp

private lemma antiDiagSum_flipVertical' (M : Square n \u03b1) :
    antiDiagSum (flipVertical M) = diagSum M := by
  simp only [antiDiagSum, diagSum, flipVertical]
  rw [\u2190 Function.Bijective.sum_comp Fin.rev_bijective (fun i => M i i)]

private lemma rowSum_flipHorizontal' (M : Square n \u03b1) (i : Fin n) :
    rowSum (flipHorizontal M) i = rowSum M i := by
  simp only [rowSum, flipHorizontal]
  rw [\u2190 Function.Bijective.sum_comp Fin.rev_bijective (fun j => M i j)]

private lemma colSum_flipHorizontal' (M : Square n \u03b1) (j : Fin n) :
    colSum (flipHorizontal M) j = colSum M (Fin.rev j) := by
  simp [colSum, flipHorizontal]

private lemma diagSum_flipHorizontal' (M : Square n \u03b1) :
    diagSum (flipHorizontal M) = antiDiagSum M := by
  simp only [diagSum, antiDiagSum, flipHorizontal]

private lemma antiDiagSum_flipHorizontal' (M : Square n \u03b1) :
    antiDiagSum (flipHorizontal M) = diagSum M := by
  simp [antiDiagSum, diagSum, flipHorizontal]

end helpers
"""

SOL_TOTAL = """
/-- The total is the sum of the `n` row sums, each equal to `s`. -/
theorem solution {n : \u2115} {\u03b1 : Type*} [AddCommMonoid \u03b1]
    (M : Square n \u03b1) (s : \u03b1) (hM : IsSemiMagic M s) :
    totalSum M = n \u2022 s := by
  calc
    totalSum M = \u2211 i : Fin n, rowSum M i := by simp [totalSum, rowSum]
    _ = \u2211 i : Fin n, s := by simp [hM.1]
    _ = n \u2022 s := by
          rw [Finset.sum_const, Finset.card_univ]
          simp
"""

SOL_TRANSPOSE = """
/-- Rows and columns are exchanged; both diagonals are fixed. -/
theorem solution {n : \u2115} {\u03b1 : Type*} [AddCommMonoid \u03b1]
    (M : Square n \u03b1) (s : \u03b1) (hM : IsMagic M s) :
    IsMagic (transpose M) s := by
  constructor
  \u00b7 constructor
    \u00b7 intro i
      simpa [rowSum_transpose'] using hM.1.2 i
    \u00b7 intro j
      simpa [colSum_transpose'] using hM.1.1 j
  \u00b7 constructor
    \u00b7 simpa [diagSum_transpose'] using hM.2.1
    \u00b7 simpa [antiDiagSum_transpose'] using hM.2.2
"""

SOL_FV = """
/-- Rows go to rows, columns to columns, and the two diagonals swap. -/
theorem solution {n : \u2115} {\u03b1 : Type*} [AddCommMonoid \u03b1]
    (M : Square n \u03b1) (s : \u03b1) (hM : IsMagic M s) :
    IsMagic (flipVertical M) s := by
  constructor
  \u00b7 constructor
    \u00b7 intro i
      simpa [rowSum_flipVertical'] using hM.1.1 (Fin.rev i)
    \u00b7 intro j
      simpa [colSum_flipVertical'] using hM.1.2 j
  \u00b7 constructor
    \u00b7 simpa [diagSum_flipVertical'] using hM.2.2
    \u00b7 simpa [antiDiagSum_flipVertical'] using hM.2.1
"""

SOL_FH = """
/-- Columns go to columns, rows to rows, and the two diagonals swap. -/
theorem solution {n : \u2115} {\u03b1 : Type*} [AddCommMonoid \u03b1]
    (M : Square n \u03b1) (s : \u03b1) (hM : IsMagic M s) :
    IsMagic (flipHorizontal M) s := by
  constructor
  \u00b7 constructor
    \u00b7 intro i
      simpa [rowSum_flipHorizontal'] using hM.1.1 i
    \u00b7 intro j
      simpa [colSum_flipHorizontal'] using hM.1.2 (Fin.rev j)
  \u00b7 constructor
    \u00b7 simpa [diagSum_flipHorizontal'] using hM.2.2
    \u00b7 simpa [antiDiagSum_flipHorizontal'] using hM.2.1
"""

SOL_AFFINE = """
/-- Every line has `n` entries, so its sum becomes `a * s + n \u2022 b`. -/
theorem solution {n : \u2115} {\u03b1 : Type*} [Semiring \u03b1]
    (M : Square n \u03b1) (s a b : \u03b1) (hM : IsMagic M s) :
    IsMagic (affine a b M) (a * s + n \u2022 b) := by
  constructor
  \u00b7 constructor
    \u00b7 intro i
      rw [rowSum_affine]
      rw [hM.1.1 i]
      ring
    \u00b7 intro j
      rw [colSum_affine]
      rw [hM.1.2 j]
      ring
  \u00b7 constructor
    \u00b7 rw [diagSum_affine]
      rw [hM.2.1]
      ring
    \u00b7 rw [antiDiagSum_affine]
      rw [hM.2.2]
      ring
"""

SOL_OPPOSITE = """
/-- Expand the nine line identities; each opposite pair sits on one of them. -/
theorem solution
    (M : Square 3 \u2115) (s : \u2115) (hM : IsMagic M s) (i j : Fin 3) :
    M i j + M (Fin.rev i) (Fin.rev j) = 2 * M 1 1 := by
  have hR0 := hM.1.1 (0 : Fin 3)
  have hR1 := hM.1.1 (1 : Fin 3)
  have hR2 := hM.1.1 (2 : Fin 3)
  have hC0 := hM.1.2 (0 : Fin 3)
  have hC1 := hM.1.2 (1 : Fin 3)
  have hC2 := hM.1.2 (2 : Fin 3)
  have hD := hM.2.1
  have hA := hM.2.2
  simp [rowSum, colSum, diagSum, antiDiagSum, Fin.sum_univ_three] at *
  fin_cases i <;> fin_cases j <;> omega
"""

ITEMS = [
    ("Sol_MagicSquares_total_sum_eq_n_line_sum.lean", HEAD_BASE, None, SOL_TOTAL),
    ("Sol_MagicSquares_transpose_preserves_magic.lean", HEAD_TRA, HELPERS, SOL_TRANSPOSE),
    ("Sol_MagicSquares_flipVertical_preserves_magic.lean", HEAD_TRA, HELPERS, SOL_FV),
    ("Sol_MagicSquares_flipHorizontal_preserves_magic.lean", HEAD_TRA, HELPERS, SOL_FH),
    ("Sol_MagicSquares_affine_preserves_magic.lean", HEAD_TRA, None, SOL_AFFINE),
    ("Sol_MagicSquares_order_three_opposite_sum_eq_twice_center.lean", HEAD_BASE, None, SOL_OPPOSITE),
]

for fname, head, helpers, body in ITEMS:
    text = head
    if helpers:
        text += helpers
    text += body
    path = os.path.join(ROOT, "Solutions", fname)
    with io.open(path, "w", encoding="utf-8") as fh:
        fh.write(text)
    print("wrote", fname)
