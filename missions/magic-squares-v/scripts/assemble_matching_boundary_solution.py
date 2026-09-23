#!/usr/bin/env python
"""Assemble the complete proof of the published matching-boundary child."""

from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[3]
SRC = ROOT / "examples" / "magic-squares" / "spencer"
OUT = ROOT / "Solutions" / "Sol_MagicSquares_matching_boundary_euler.lean"
ROOT_MODULE = "MatchingIntervalEuler"

LOCAL_IMPORT = re.compile(
    r"^import examples\.\«magic-squares\»\.spencer\.([A-Za-z0-9_]+)\s*$",
    re.MULTILINE,
)
IMPORT_RE = re.compile(r"^import .*$", re.MULTILINE)
PUBLIC_DEFINITION_IMPORT = re.compile(r"^import (Definitions\.[^\s]+)\s*$", re.MULTILINE)

TAIL = """
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    MagicSquaresBoundary.MatchingBoundaryCriterion n := by
  exact MagicSquaresBoundary.matchingBoundaryCriterion_proved n hn
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
        path = SRC / f"{name}.lean"
        if not path.is_file():
            raise RuntimeError(f"missing local dependency {path}")
        active.add(name)
        source = path.read_text(encoding="utf-8")
        if re.search(r"^import Theorems\.", source, re.MULTILINE):
            raise RuntimeError(f"forbidden theorem import in {name}")
        for dependency in LOCAL_IMPORT.findall(source):
            visit(dependency)
        active.remove(name)
        done.add(name)
        order.append(name)

    visit(root)
    return order


def main() -> None:
    modules = dependency_order(ROOT_MODULE)
    public_imports: set[str] = set()
    sources: list[tuple[str, str]] = []
    for name in modules:
        source = (SRC / f"{name}.lean").read_text(encoding="utf-8")
        public_imports.update(PUBLIC_DEFINITION_IMPORT.findall(source))
        sources.append((name, IMPORT_RE.sub("", source).strip()))

    header_lines = ["import Mathlib"]
    header_lines.extend(f"import {name}" for name in sorted(public_imports))
    header_lines.extend([
        "",
        "set_option autoImplicit false",
        "attribute [local instance] Classical.propDecidable",
        "",
    ])
    parts = ["\n".join(header_lines)]
    for name, source in sources:
        parts.extend((f"/-! From {name}.lean -/", source, ""))
    parts.append(TAIL)
    output = "\n".join(parts)

    assert output.count("import Mathlib") == 1
    assert "import examples." not in output and "import Theorems." not in output
    assert not re.search(r"\b(sorry|admit|native_decide)\b", output)
    assert len(re.findall(r"^theorem solution\b", output, re.MULTILINE)) == 1
    assert "namespace " not in TAIL and "end " not in TAIL
    for public_import in public_imports:
        assert len(re.findall(
            rf"^import {re.escape(public_import)}$", output, re.MULTILINE)) == 1

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(output, encoding="utf-8")
    print("modules: " + ", ".join(modules))
    print("public imports: " + ", ".join(sorted(public_imports)))
    print(f"wrote {OUT.relative_to(ROOT)} ({output.count(chr(10)) + 1} lines)")


if __name__ == "__main__":
    main()
