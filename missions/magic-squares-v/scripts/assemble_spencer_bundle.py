#!/usr/bin/env python
"""Assemble the eight spencer modules into one platform-submittable solution file.

The platform compiles the file as a standalone module, so the bundle keeps exactly one
import header (`Mathlib` + `Definitions.Def_MagicSquares`, the only two the platform
allows) and then concatenates the module bodies in topological order.  Every module keeps
its own `namespace MagicSquaresSpencer ... end MagicSquaresSpencer` block; reopening the
same namespace is legal in Lean, and it is how `Sol_*` bundles have been built all along.

The last thing in the file is the top-level `theorem solution`, whose type must agree with
the problem statement registered on the platform.
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
SRC = ROOT / "examples" / "magic-squares" / "spencer"

# topological order: each module only imports the ones before it
MODULES = ["Spencer", "HallSupport", "SupportSplit", "Recursion",
           "Aggregate", "Rank", "Sharp", "Degree"]

OUT = ROOT / "Solutions" / "Sol_MagicSquares_semi_magic_polynomial_exists_degree_eq.lean"

HEADER = """\
import Mathlib
import Definitions.Def_MagicSquares

/-!
# Spencer's theorem with the exact degree, assembled for the platform

Bundle of `examples/magic-squares/spencer/*` (bricks 1-11):

* `Spencer.lean`     - discrete antiderivative, the Spencer step
* `HallSupport.lean` - Hall: a positive line-sum matrix contains a permutation
* `SupportSplit.lean`- the split `T |-> T - P` and the fibre recurrence
* `Recursion.lean`   - the recurrence with constant coefficients; `gB` is polynomial
* `Aggregate.lean`   - the bridge to `semiMagicCount`; the crude `n * n` bound
* `Rank.lean`        - `rankB`, the face rank as `dim (zero-line-sum space)`
* `Sharp.lean`       - the sharp upper bound `natDegree <= (n - 1) ^ 2`
* `Degree.lean`      - the matching lower bound, giving degree exactly `(n - 1) ^ 2`

The single deviation from the mission goal `MagicSquares.semi_magic_polynomial_exists` is
the hypothesis `1 <= t`: the support-set recursion of Spencer's proof has no term for the
empty support, so the value at line sum `0` (equivalently Ehrhart-Macdonald reciprocity at
`-1`) is not reachable by this route.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open Finset
open MagicSquares
open scoped BigOperators

"""

TAIL = """

/-! ## The platform-facing statement -/

/-- Spencer's theorem with the exact degree, in the mission's own vocabulary.

For every order `n >= 1` there is a rational polynomial of degree exactly `(n - 1) ^ 2`
that counts the `n x n` semi-magic squares of line sum `t` for every `t >= 1`.

This is `MagicSquares.semi_magic_polynomial_exists` with the hypothesis `1 <= t` added;
agreement at `t = 0` is the reciprocity rung and is not claimed here. -/
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : Polynomial ℚ, p.natDegree = (n - 1) ^ 2 ∧
      ∀ t : ℕ, 1 ≤ t → p.eval (t : ℚ) = (semiMagicCount n t : ℚ) :=
  MagicSquaresSpencer.exists_polynomial_semiMagicCount_degree_eq n hn
"""

IMPORT_RE = re.compile(r"^import .*$", re.MULTILINE)


def body(name):
    text = (SRC / (name + ".lean")).read_text(encoding="utf-8")
    stripped = IMPORT_RE.sub("", text)
    # collapse the blank run the import removal leaves behind
    stripped = re.sub(r"\n{3,}", "\n\n", stripped).strip("\n")
    return stripped


parts = [HEADER]
for m in MODULES:
    parts.append("-- " + "=" * 74)
    parts.append("-- from spencer/%s.lean" % m)
    parts.append("-- " + "=" * 74)
    parts.append("")
    parts.append(body(m))
    parts.append("")
parts.append(TAIL)

assembled = "\n".join(parts)
# structural assertions: the endpoint and the two imports must be present
assert "theorem solution (n : ℕ) (hn : 1 ≤ n)" in assembled, "solution theorem missing"
assert "exists_polynomial_semiMagicCount_degree_eq" in assembled, "endpoint not used"
assert assembled.count("import Mathlib") == 1, "duplicate Mathlib import"
assert assembled.count("import Definitions.Def_MagicSquares") == 1, "duplicate defs import"
assert "import examples." not in assembled, "a local import survived"
assert "sorry" not in assembled and "admit" not in assembled, "sorry/admit in the bundle"

OUT.write_text(assembled, encoding="utf-8")
print("wrote %s" % OUT.relative_to(ROOT))
print("lines: %d" % assembled.count("\n"))
print("namespace blocks: %d" % assembled.count("namespace MagicSquaresSpencer"))
