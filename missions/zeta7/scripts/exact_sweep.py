"""Bounded parameter sweep of primitive integer Hankel polynomials."""
from __future__ import annotations

import json
from pathlib import Path
import time

from exact_hankel import ROOT, evaluate, parameters, record


def main():
    out = ROOT / "missions/zeta7/verification/exact_sweep.jsonl"
    out.parent.mkdir(parents=True, exist_ok=True)
    cases = []
    for K in (8, 12, 16, 20, 24):
        ns = sorted({max(1, round(K * alpha)) for alpha in (.075, .15, .25, .35)})
        for N in ns:
            for q in (2, 3, 4, 5):
                cases.append((7, K, N, q))
    # Matched ζ(5) baseline and larger ζ(7) probes.
    for K, N in ((8, 1), (12, 1), (16, 1), (20, 2), (24, 2), (32, 2), (40, 3)):
        cases.append((5, K, N, 3))
        cases.append((7, K, N, 3))
    for K, N in ((32, 2), (40, 3)):
        for q in (2, 4, 5):
            cases.append((7, K, N, q))
    seen = set()
    with out.open("w", encoding="utf-8") as stream:
        for case in cases:
            if case in seen:
                continue
            seen.add(case)
            start = time.monotonic()
            try:
                r = parameters(*case)
                row = record(r, evaluate(r), False)
                row["seconds"] = round(time.monotonic() - start, 3)
                stream.write(json.dumps(row) + "\n")
                stream.flush()
                print("s,K,N,q=" + ",".join(map(str, case)),
                      "log(P)/K^2=", round(row["log_value_per_K2"], 6),
                      "time=", row["seconds"], flush=True)
            except Exception as e:
                row = dict(s=case[0], K=case[1], N=case[2], q=case[3],
                           error=type(e).__name__ + ": " + str(e),
                           seconds=round(time.monotonic() - start, 3))
                stream.write(json.dumps(row) + "\n")
                stream.flush()
                print("FAILED", row, flush=True)


if __name__ == "__main__":
    main()
