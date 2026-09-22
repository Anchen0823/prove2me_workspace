#!/usr/bin/env python
"""Assemble the semi-magic cone face/support order isomorphism for submission."""

from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[3]
SRC = ROOT / "examples" / "magic-squares" / "spencer"
OUT = ROOT / "Solutions" / "Sol_MagicSquares_real_cone_face_support_order_iso.lean"
MODULES = (
    "OrthantFace",
    "OrthantFaceSupport",
    "OrthantCoordinateFace",
    "OrthantFaceOrder",
    "BirkhoffSupport",
    "DoublyStochasticSupport",
    "SemiMagicCone",
    "SemiMagicFaceSupport",
)

HEADER = """\
import Mathlib
import Definitions.Def_MagicSquaresRealCone
import Definitions.Def_MagicSquaresMatchingBoundary

set_option autoImplicit false

"""

TAIL = """
/-! Platform-facing face/support theorem. -/

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ∃ e :
      {F : PointedCone ℝ ((Fin n × Fin n) → ℝ) //
        F.IsFaceOf (MagicSquaresRealCone.cone n)} ≃o
      {B : Finset (Fin n × Fin n) //
        B = ∅ ∨ MagicSquaresBoundary.MatchingCoveredBoard n B},
      ∀ F i, i ∈ (e F).val ↔ ∃ x ∈ F.val, x i ≠ 0 := by
  change ∃ e :
      {F : PointedCone ℝ ((Fin n × Fin n) → ℝ) //
        F.IsFaceOf (MagicSquaresGeometry.orthantSection
          (MagicSquaresGeometry.semiMagicSubspace n))} ≃o
      {B : Finset (Fin n × Fin n) //
        B = ∅ ∨ MagicSquaresBoundary.MatchingCoveredBoard n B},
      ∀ F i, i ∈ (e F).val ↔ ∃ x ∈ F.val, x i ≠ 0
  refine ⟨MagicSquaresGeometry.semiMagicFaceSupportOrderIso n hn, ?_⟩
  intro F i
  exact MagicSquaresGeometry.mem_faceSupport F.val i
"""


def main() -> None:
    parts = [HEADER]
    for name in MODULES:
        source = (SRC / f"{name}.lean").read_text(encoding="utf-8")
        source = re.sub(r"^import .*$", "", source, flags=re.MULTILINE).strip()
        parts.extend((f"/-! From {name}.lean -/", source, ""))
    parts.append(TAIL)
    output = "\n".join(parts)
    assert output.count("import Mathlib") == 1
    assert output.count("import Definitions.Def_MagicSquaresRealCone") == 1
    assert output.count("import Definitions.Def_MagicSquaresMatchingBoundary") == 1
    assert "import examples." not in output
    assert "sorry" not in output and "admit" not in output
    OUT.write_text(output, encoding="utf-8")
    print(f"wrote {OUT.relative_to(ROOT)} ({output.count(chr(10)) + 1} lines)")


if __name__ == "__main__":
    main()
