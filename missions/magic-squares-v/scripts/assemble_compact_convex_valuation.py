#!/usr/bin/env python
"""Assemble the compact-convex indicator relation from proved local modules."""

from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[3]
SRC = ROOT / "examples" / "magic-squares" / "spencer"
OUT = ROOT / "Solutions" / "Sol_ConvexGeometry_compact_convex_indicator_relation.lean"

MODULES = [
    "ClosedIntervalIndicator",
    "ClosedIntervalValuation",
    "CompactRealValuation",
    "CompactConvexProjection",
    "CompactConvexSlices",
    "CompactConvexValuation",
]

IMPORT_RE = re.compile(r"^import .*$", re.MULTILINE)

HEADER = """\
import Mathlib

set_option autoImplicit false
attribute [local instance] Classical.propDecidable

"""

TAIL = """
theorem solution (n : ℕ)
    {ι : Type*} [Fintype ι] (K : ι → Set (Fin n → ℝ)) (w : ι → ℚ)
    (hc : ∀ i, IsCompact (K i)) (hv : ∀ i, Convex ℝ (K i))
    (h : ∀ x, (∑ i, if x ∈ K i then w i else 0) = 0) :
    (∑ i, if (K i).Nonempty then w i else 0) = 0 := by
  exact MagicSquaresEuler.compactConvex_indicator_relation n K w hc hv h
"""


def main() -> None:
    parts = [HEADER]
    for name in MODULES:
        path = SRC / f"{name}.lean"
        source = path.read_text(encoding="utf-8")
        if re.search(r"^import Theorems\.", source, re.MULTILINE):
            raise RuntimeError(f"forbidden theorem import in {name}")
        source = IMPORT_RE.sub("", source).strip()
        parts.extend((f"/-! From {name}.lean -/", source, ""))
    parts.append(TAIL)
    output = "\n".join(parts)

    assert output.count("import Mathlib") == 1
    assert "import examples." not in output and "import Theorems." not in output
    assert "CompactConvexValuation" not in IMPORT_RE.findall(output)
    assert not re.search(r"\b(sorry|admit|native_decide)\b", output)
    assert len(re.findall(r"^theorem solution\b", output, re.MULTILINE)) == 1
    assert "namespace " not in TAIL and "end " not in TAIL

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(output, encoding="utf-8")
    print("modules: " + ", ".join(MODULES))
    print(f"wrote {OUT.relative_to(ROOT)} ({output.count(chr(10)) + 1} lines)")


if __name__ == "__main__":
    main()
