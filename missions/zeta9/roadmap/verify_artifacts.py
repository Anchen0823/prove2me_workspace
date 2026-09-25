"""Check frozen round 1–9 manifests and the current roadmap artifact manifest."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


BASE = Path(__file__).resolve().parent
ZETA9 = BASE.parent
CURRENT = BASE / "verification/artifact-manifest.json"


def records(directory: Path) -> list[dict[str, object]]:
    result = []
    for path in sorted(directory.rglob("*")):
        if not path.is_file() or "__pycache__" in path.parts:
            continue
        if path == directory / "verification/artifact-manifest.json":
            continue
        raw = path.read_bytes()
        result.append({
            "path": path.relative_to(directory).as_posix(),
            "bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest(),
        })
    return result


def verify(directory: Path, manifest: Path) -> int:
    expected = json.loads(manifest.read_text(encoding="utf-8"))
    actual = []
    for entry in expected:
        path = (directory / entry["path"]).resolve()
        assert path.is_relative_to(directory.resolve()) and path.is_file(), path
        raw = path.read_bytes()
        actual.append({
            "path": entry["path"],
            "bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest(),
        })
    assert expected == actual, f"Manifest mismatch: {manifest}"
    if directory == BASE:
        assert expected == records(BASE), "Roadmap manifest does not list every current file"
    return len(expected)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write-current", action="store_true")
    args = parser.parse_args()

    if args.write_current:
        CURRENT.write_text(
            json.dumps(records(BASE), ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )

    total = 0
    total += verify(ZETA9, ZETA9 / "verification/artifact-manifest.json")
    for round_number in range(2, 10):
        directory = ZETA9 / f"round{round_number}"
        total += verify(directory, directory / "verification/artifact-manifest.json")
    current = verify(BASE, CURRENT)
    print(f"verified {total} frozen files across rounds 1-9 and {current} roadmap files")


if __name__ == "__main__":
    main()
