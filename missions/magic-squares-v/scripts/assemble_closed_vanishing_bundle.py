#!/usr/bin/env python
"""Assemble the closed-support negative-root proof into the live vanishing target."""

from assemble_closed_support_bundle import MODULES as POLY_MODULES, OUT as POLY_OUT, ROOT, body


OUT = ROOT / "Solutions" / "Sol_MagicSquares_semi_magic_vanishing.lean"
MODULES = POLY_MODULES + ["ClosedEvaluation", "CyclicPermutations", "ClosedVanishing"]

HEADER = """\
import Mathlib
import Definitions.Def_MagicSquares

/-!
# Negative roots of the semi-magic counting polynomial

Standalone platform bundle.  It develops the closed-support counting polynomial,
extends its finite-difference recurrence to rational arguments, and uses disjoint
cyclic permutation supports to prove the full vanishing list at
`-1, ..., -(n-1)`.  It makes no claim about Ehrhart-Macdonald reciprocity.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset
open MagicSquares
open scoped BigOperators

"""

TAIL = """

/-! ## Platform-facing theorem -/

theorem solution (n : ℕ) (hn : 1 ≤ n) (p : Polynomial ℚ)
    (hp : ∀ t : ℕ, p.eval (t : ℚ) = (semiMagicCount n t : ℚ)) :
    ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) - 1 → p.eval (-(k : ℚ)) = 0 :=
  MagicSquaresSpencer.semiMagic_polynomial_vanishing n hn p hp
"""


def main() -> None:
    missing = [name for name in MODULES if not
               (ROOT / "examples" / "magic-squares" / "spencer" / (name + ".lean")).is_file()]
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

    assert OUT != POLY_OUT
    assert "theorem solution (n : ℕ) (hn : 1 ≤ n) (p : Polynomial ℚ)" in assembled
    assert "semiMagic_polynomial_vanishing n hn p hp" in assembled
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
