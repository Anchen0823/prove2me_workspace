#!/usr/bin/env python
"""Build a standalone Mathlib proof of the coordinate-face classification."""

from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[3]
SRC = ROOT / "examples" / "magic-squares" / "spencer"
OUT = ROOT / "Solutions" / "Sol_Orthant_coordinate_face.lean"
MODULES = ("OrthantFace", "OrthantFaceSupport", "OrthantCoordinateFace")

HEADER = """\
import Mathlib

set_option autoImplicit false

"""

TAIL = """
/-! A platform-facing statement using Mathlib types and operations only. -/

theorem solution {𝕜 ι : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [Fintype ι]
    (L : Submodule 𝕜 (ι → 𝕜)) (F : PointedCone 𝕜 (ι → 𝕜)) :
    F.IsFaceOf (PointedCone.ofSubmodule L ⊓ PointedCone.positive 𝕜 (ι → 𝕜)) ↔
      ∃ B : Set ι, ∀ x : ι → 𝕜,
        (x ∈ F ↔
          x ∈ (PointedCone.ofSubmodule L ⊓ PointedCone.positive 𝕜 (ι → 𝕜)) ∧
            ∀ i, i ∉ B → x i = 0) := by
  constructor
  · intro hF
    obtain ⟨B, hEq⟩ := (MagicSquaresGeometry.isFaceOf_iff_coordinateFace L F).mp hF
    refine ⟨B, fun x => ?_⟩
    rw [hEq]
    exact MagicSquaresGeometry.mem_coordinateFace L B x
  · rintro ⟨B, hB⟩
    apply (MagicSquaresGeometry.isFaceOf_iff_coordinateFace L F).mpr
    refine ⟨B, ?_⟩
    ext x
    exact (hB x).trans (MagicSquaresGeometry.mem_coordinateFace L B x).symm
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
    assert "import examples." not in output
    assert "sorry" not in output and "admit" not in output
    OUT.write_text(output, encoding="utf-8")
    print(f"wrote {OUT.relative_to(ROOT)} ({output.count(chr(10)) + 1} lines)")


if __name__ == "__main__":
    main()
