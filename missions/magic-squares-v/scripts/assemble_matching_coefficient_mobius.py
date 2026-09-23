#!/usr/bin/env python
"""Assemble the matching coefficient / Möbius theorem from local Spencer modules."""

from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[3]
SRC = ROOT / "examples" / "magic-squares" / "spencer"
OUT = ROOT / "Solutions" / "Sol_MagicSquares_matching_coefficient_eq_neg_mobius.lean"
ROOT_MODULE = "MatchingMobius"
LOCAL_IMPORT = re.compile(
    r'^import examples\.\«magic-squares\»\.spencer\.([A-Za-z0-9_]+)\s*$', re.MULTILINE)
IMPORT_RE = re.compile(r"^import .*$", re.MULTILINE)

HEADER = """\
import Mathlib
import Definitions.Def_MagicSquares
import Definitions.Def_MagicSquaresMatchingBoundary

set_option autoImplicit false
attribute [local instance] Classical.propDecidable

"""

TAIL = """
theorem solution (n : ℕ) (hn : 1 ≤ n)
    (B : Finset (Fin n × Fin n))
    (hB : MagicSquaresBoundary.MatchingCoveredBoard n B) :
    MagicSquaresBoundary.matchingEulerCoefficient n B =
      -IncidenceAlgebra.mu ℚ
        (⟨∅, Or.inl rfl⟩ :
          {C : Finset (Fin n × Fin n) //
            C = ∅ ∨ MagicSquaresBoundary.MatchingCoveredBoard n C})
        ⟨B, Or.inr hB⟩ := by
  let B' : MagicSquaresBoundary.MatchingBoard n := ⟨B, Or.inr hB⟩
  have hne : B' ≠ ⊥ := by
    intro h
    have hempty : B = ∅ :=
      (MagicSquaresBoundary.matchingBoard_eq_bot_iff n B').mp h
    exact hB.1.ne_empty hempty
  exact MagicSquaresBoundary.matchingEulerCoefficient_eq_neg_mu n hn B' hne
"""


def dependency_order(root: str) -> list[str]:
    done: set[str] = set()
    active: set[str] = set()
    order: list[str] = []

    def visit(name: str) -> None:
        if name in done:
            return
        if name in active:
            raise RuntimeError(f"dependency cycle at {name}")
        active.add(name)
        path = SRC / f"{name}.lean"
        text = path.read_text(encoding="utf-8")
        if re.search(r"^import Theorems\.", text, re.MULTILINE):
            raise RuntimeError(f"forbidden theorem import in {name}")
        for dep in LOCAL_IMPORT.findall(text):
            visit(dep)
        active.remove(name)
        done.add(name)
        order.append(name)

    visit(root)
    return order


def main() -> None:
    modules = dependency_order(ROOT_MODULE)
    parts = [HEADER]
    for name in modules:
        source = (SRC / f"{name}.lean").read_text(encoding="utf-8")
        source = IMPORT_RE.sub("", source).strip()
        parts.extend((f"/-! From {name}.lean -/", source, ""))
    parts.append(TAIL)
    output = "\n".join(parts)
    assert output.count("import Mathlib") == 1
    assert len(re.findall(r"^import Definitions\.Def_MagicSquares$", output, re.MULTILINE)) == 1
    assert len(re.findall(r"^import Definitions\.Def_MagicSquaresMatchingBoundary$", output,
                          re.MULTILINE)) == 1
    assert "import examples." not in output and "import Theorems." not in output
    assert "sorry" not in output and "admit" not in output and "native_decide" not in output
    assert len(re.findall(r"^theorem solution\b", output, re.MULTILINE)) == 1
    assert "namespace " not in TAIL and "end " not in TAIL
    OUT.write_text(output, encoding="utf-8")
    print("modules: " + ", ".join(modules))
    print(f"wrote {OUT.relative_to(ROOT)} ({output.count(chr(10)) + 1} lines)")


if __name__ == "__main__":
    main()
