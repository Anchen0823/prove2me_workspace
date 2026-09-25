"""Finite exact sweep over Hankel size independent of pole count."""
from __future__ import annotations

import json
from pathlib import Path
import time

from exact_hankel import ROOT, evaluate, parameters, record


def main():
    out = ROOT / "missions/zeta7/verification/exact_h_sweep.jsonl"
    cases = []
    for K, N in ((8, 1), (12, 1), (16, 1), (16, 2), (20, 2)):
        r = K - N
        for factor in (.5, .75, 1, 1.25, 1.5, 2):
            h = max(1, round(r * factor))
            for q in (1, 2, 3, 4):
                cases.append((7, K, N, q, h))
    with out.open("w", encoding="utf-8") as stream:
        for case in cases:
            start = time.monotonic()
            try:
                r = parameters(*case)
                row = record(r, evaluate(r), False)
                row["seconds"] = round(time.monotonic() - start, 3)
            except Exception as e:
                row = dict(s=case[0], K=case[1], N=case[2], q=case[3], h=case[4],
                           error=type(e).__name__ + ": " + str(e),
                           seconds=round(time.monotonic() - start, 3))
            stream.write(json.dumps(row) + "\n")
            stream.flush()
            print("K,N,q,h=", case[1:], "log(P)/K^2=", row.get("log_value_per_K2"),
                  "time=", row["seconds"], flush=True)


if __name__ == "__main__":
    main()
