#!/usr/bin/env python
"""Assemble the conditional semi-magic reciprocity reduction as one Lean file."""

from assemble_closed_support_bundle import MODULES as POLY_MODULES, ROOT, SRC, body


OUT = ROOT / "Solutions" / "Sol_MagicSquares_semi_magic_reciprocity_boundary.lean"

# Every local import is supplied by an earlier body. The negative-root module is
# included because ReciprocityFromBoundary contains the conditional root theorem.
MODULES = POLY_MODULES + [
    "ClosedEvaluation",
    "SupportPartition",
    "SupportExactIE",
    "SupportCoverage",
    "SupportConstants",
    "PositiveTranslation",
    "FirstNegativeValue",
    "PolynomialDifference",
    "ReciprocityPropagation",
    "FiniteBoundaryBalance",
    "ReflectionSign",
    "ReflectionExtension",
    "CyclicPermutations",
    "ClosedVanishing",
    "ReciprocityFromBoundary",
    "MatchingBoundaryCriterion",
]

HEADER = """\
import Mathlib
import Definitions.Def_MagicSquares
import Theorems.Thm_MagicSquares_matching_boundary_euler

/-!
# Conditional semi-magic reciprocity from finite boundary balance

Standalone platform reduction. The finite matching criterion is supplied by
the separate child theorem; all polynomial and counting steps are proved here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

open Finset
open MagicSquares
open scoped BigOperators

"""

TAIL = """

/-! ## Adapter from the public finite predicate -/

theorem matching_boundary_adapter (n : ℕ)
    (h : MagicSquaresBoundary.MatchingBoundaryCriterion n) :
    MagicSquaresSpencer.MatchingBoundaryCriterion n := by
  have hcoeff (B : Finset (Fin n × Fin n)) :
      MagicSquaresBoundary.matchingEulerCoefficient n B =
        MagicSquaresSpencer.matchingEulerCoefficient n B := by
    classical
    simp only [MagicSquaresBoundary.matchingEulerCoefficient,
      MagicSquaresSpencer.matchingEulerCoefficient]
    apply Finset.sum_congr rfl
    intro S hS
    have heq : MagicSquaresBoundary.HasPerm n (B \\ S) ↔
        MagicSquaresSpencer.HasPerm n (B \\ S) := by
      simp only [MagicSquaresBoundary.HasPerm, MagicSquaresSpencer.HasPerm,
        MagicSquaresBoundary.permSupport, MagicSquaresSpencer.matSupport_permMatrix]
    by_cases hp : MagicSquaresBoundary.HasPerm n (B \\ S)
    · rw [if_pos hp, if_pos (heq.mp hp)]
    · rw [if_neg hp, if_neg (fun h => hp (heq.mpr h))]
  have hcand (B φ : Finset (Fin n × Fin n)) :
      MagicSquaresBoundary.fiberCandidates B φ =
        MagicSquaresSpencer.fiberCandidates B φ := by
    classical
    ext C
    simp [MagicSquaresBoundary.fiberCandidates,
      MagicSquaresSpencer.fiberCandidates]
  simpa only [MagicSquaresBoundary.MatchingBoundaryCriterion,
    MagicSquaresBoundary.MatchingCoveredBoard,
    MagicSquaresBoundary.permSupport,
    MagicSquaresSpencer.MatchingBoundaryCriterion,
    MagicSquaresSpencer.MatchingCoveredBoard,
    MagicSquaresSpencer.matSupport_permMatrix, hcoeff, hcand] using h

/-! ## Platform-facing conditional reciprocity theorem -/

theorem solution (n : ℕ) (hn : 1 ≤ n) (p : Polynomial ℚ)
    (hp : ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)) :
    ∀ t : ℤ, p.eval (((-(n : ℤ) - t : ℤ) : ℚ)) =
      (-1 : ℚ) ^ (n - 1) * p.eval (t : ℚ) := by
  have h := matching_boundary_adapter n (MagicSquares.matching_boundary_euler n hn)
  exact MagicSquaresSpencer.semiMagic_reciprocity_of_matchingBoundaryCriterion n hn p hp h
"""


def main() -> None:
    missing = [name for name in MODULES if not (SRC / (name + ".lean")).is_file()]
    if missing:
        raise SystemExit("missing modules: " + ", ".join(missing))
    if len(MODULES) != len(set(MODULES)):
        raise SystemExit("duplicate module in boundary bundle")

    parts = [HEADER]
    for name in MODULES:
        parts.extend([
            "-- " + "=" * 74,
            "-- from spencer/%s.lean" % name,
            "-- " + "=" * 74,
            "",
            body(name),
            "",
        ])
    parts.append(TAIL)
    assembled = "\n".join(parts)
    assert assembled.count("import Mathlib") == 1
    assert assembled.count("import Definitions.Def_MagicSquares") == 1
    assert assembled.count("import Theorems.Thm_MagicSquares_matching_boundary_euler") == 1
    assert "import examples." not in assembled
    assert "sorry" not in assembled and "admit" not in assembled
    assert "native_decide" not in assembled
    OUT.write_text(assembled, encoding="utf-8")
    print("wrote %s" % OUT.relative_to(ROOT))
    print("lines: %d" % assembled.count("\n"))


if __name__ == "__main__":
    main()
