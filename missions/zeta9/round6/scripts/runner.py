"""Resumable single-worker Round6 jobs; every subprocess has a 120 s cap."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[4]
SCRIPT = Path(__file__).with_name("primitive_search.py")
VERIFY = ROOT / "missions/zeta9/round6/verification"
PYTHON = Path(r"C:\Users\anche\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--phase", choices=["input", "search", "both"], default="both")
    parser.add_argument("--n", type=int, nargs="*", default=[12, 24, 48, 96, 192])
    parser.add_argument("--force", action="store_true")
    args = parser.parse_args()
    if any(n not in (12, 24, 48, 96, 192) for n in args.n):
        parser.error("Allowed n: 12,24,48,96,192")
    VERIFY.mkdir(parents=True, exist_ok=True)
    phases = ["input", "search"] if args.phase == "both" else [args.phase]
    for phase in phases:
        for n in args.n:
            artifact = VERIFY / (f"search-input-n{n}.json.gz" if phase == "input"
                                 else f"search-n{n}.json.gz")
            source_sha = hashlib.sha256(SCRIPT.read_bytes()).hexdigest()
            if artifact.exists() and not args.force:
                with __import__("gzip").open(artifact, "rt", encoding="utf-8") as stream:
                    data = json.load(stream)
                prior = data.get("source_sha256", {}).get("primitive_search")
                if prior == source_sha:
                    print(json.dumps({"phase": phase, "n": n, "status": "skipped_current"}),
                          flush=True)
                    continue
            started = time.monotonic()
            command = [str(PYTHON), str(SCRIPT), "--phase", phase, "--n", str(n)]
            try:
                result = subprocess.run(command, cwd=ROOT, capture_output=True,
                                        text=True, timeout=120)
                if result.returncode:
                    summary = {"phase": phase, "n": n, "status": "error",
                               "exit_code": result.returncode,
                               "stderr_tail": result.stderr[-4000:]}
                else:
                    summary = json.loads(result.stdout.strip())
                    summary["phase"] = phase
            except subprocess.TimeoutExpired:
                summary = {"phase": phase, "n": n, "status": "timeout_120s"}
            summary["wall_seconds"] = round(time.monotonic() - started, 3)
            with (VERIFY / "search-results.jsonl").open("a", encoding="utf-8") as stream:
                stream.write(json.dumps(summary, separators=(",", ":")) + "\n")
            print(json.dumps(summary, separators=(",", ":")), flush=True)


if __name__ == "__main__":
    main()
