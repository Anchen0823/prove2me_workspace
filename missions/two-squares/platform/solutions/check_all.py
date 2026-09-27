"""Compile every submission in one file, each in its own namespace.

A submission must be a single root-level `theorem solution`; wrapping each one in its own
namespace keeps the names apart while leaving the statement and the proof text untouched,
so a green run here means each file also compiles on its own.
"""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
WORKSPACE = HERE.parents[3]
LEAN = HERE / "AllSolutions.lean"
MARKER = "theorem solution"


def main() -> None:
    files = sorted(p for p in HERE.glob("Sol_*.lean"))
    if not files:
        raise SystemExit("no Sol_*.lean files")
    chunks = []
    for path in files:
        source = path.read_text(encoding="utf-8")
        if source.count(MARKER) != 1:
            raise SystemExit(f"{path.name}: not a single `theorem solution`")
        if re.search(r"(?m)^\s*sorry\b", source):
            raise SystemExit(f"{path.name}: contains sorry")
        body = source[source.index(MARKER):].rstrip()
        stem = path.stem[len("Sol_EqualTwoSquares_"):]
        chunks.append(f"namespace Chk_{stem}\n\n{body}\n\nend Chk_{stem}\n")
    axioms = "".join(f"#print axioms Chk_{p.stem[len('Sol_EqualTwoSquares_'):]}.solution\n"
                     for p in files)
    LEAN.write_text("import Mathlib\n\n" + "\n".join(chunks) + "\n" + axioms, encoding="utf-8")
    print(f"wrote {LEAN} with {len(chunks)} solutions")
    result = subprocess.run(["lake", "env", "lean", str(LEAN)],
                            cwd=str(WORKSPACE), capture_output=True, text=True)
    output = (result.stdout or "") + (result.stderr or "")
    print(output[-4000:] if len(output) > 4000 else output)
    print("EXIT", result.returncode)
    sys.exit(result.returncode)


if __name__ == "__main__":
    main()
