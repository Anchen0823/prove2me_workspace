#!/usr/bin/env python
"""Assemble the closed-support extension into the live polynomiality target.

The platform accepts a standalone file, not local imports.  This script retains
only the two platform imports, strips local imports from the topologically ordered
Spencer modules, and ends with the exact live `semi_magic_polynomial_exists`
statement.  Run it only after every module in MODULES compiles locally.
"""
import pathlib
import re


ROOT = pathlib.Path(__file__).resolve().parents[3]
SRC = ROOT / "examples" / "magic-squares" / "spencer"
OUT = ROOT / "Solutions" / "Sol_MagicSquares_semi_magic_polynomial_exists.lean"

# Each local import is satisfied by an earlier element.  ClosedPolynomial is
# deliberately last: it combines the closed fibres, inclusion-exclusion,
# polynomial recurrence, and the existing S5-to-degree bridge.
MODULES = [
    "Spencer",
    "PolynomialRecurrence",
    "HallSupport",
    "SupportSplit",
    "Recursion",
    "Aggregate",
    "ClosedSupport",
    "Rank",
    "Sharp",
    "Degree",
    "S5",
    "S5Bridge",
    "ClosedSupportIE",
    "ClosedPolynomial",
]

HEADER = """\
import Mathlib
import Definitions.Def_MagicSquares

/-!
# Semi-magic counting polynomial at every nonnegative line sum

Standalone platform bundle.  It follows Spencer's positive-line-sum support
recursion and extends it at line sum zero through closed support fibres and
inclusion-exclusion.  It proves polynomiality and exact degree only; it makes
no claim about Ehrhart-Macdonald reciprocity or the negative-value vanishing
list.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset
open MagicSquares
open scoped BigOperators

"""

TAIL = """

/-! ## Platform-facing theorem -/

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : Polynomial ℚ,
      p.natDegree = (n - 1) ^ 2 ∧
        ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ) :=
  MagicSquaresSpencer.exists_polynomial_semiMagicCount_all_degree_eq n hn
"""

IMPORT_RE = re.compile(r"^import .*$", re.MULTILINE)


def body(name: str) -> str:
    text = (SRC / (name + ".lean")).read_text(encoding="utf-8")
    stripped = IMPORT_RE.sub("", text)
    return re.sub(r"\n{3,}", "\n\n", stripped).strip("\n")


def main() -> None:
    missing = [name for name in MODULES if not (SRC / (name + ".lean")).is_file()]
    if missing:
        raise SystemExit("missing modules: " + ", ".join(missing))

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

    assert "theorem solution (n : ℕ) (hn : 1 ≤ n)" in assembled
    assert "exists_polynomial_semiMagicCount_all_degree_eq" in assembled
    assert assembled.count("import Mathlib") == 1
    assert assembled.count("import Definitions.Def_MagicSquares") == 1
    assert "import examples." not in assembled
    assert "sorry" not in assembled and "admit" not in assembled

    OUT.write_text(assembled, encoding="utf-8")
    print("wrote %s" % OUT.relative_to(ROOT))
    print("lines: %d" % assembled.count("\n"))
    print("namespace blocks: %d" % assembled.count("namespace MagicSquaresSpencer"))


if __name__ == "__main__":
    main()
