"""Focused exact h<tail-size experiment at larger K."""
from __future__ import annotations

import json
import time

from exact_hankel import ROOT, evaluate, parameters, record


def main():
    out = ROOT / "missions/zeta7/verification/exact_h_large.jsonl"
    cases = []
    for K, N in ((24, 2), (32, 2), (40, 3)):
        r = K - N
        for f in (.55, .7, .85):
            h = round(r * f)
            for q in (2, 3, 4, 5, 6):
                cases.append((7, K, N, q, h))
    with out.open("w", encoding="utf-8") as stream:
        for case in cases:
            start = time.monotonic()
            try:
                result = parameters(*case)
                row = record(result, evaluate(result), False)
                row["seconds"] = round(time.monotonic() - start, 3)
            except Exception as e:
                row = dict(s=case[0], K=case[1], N=case[2], q=case[3], h=case[4],
                           error=type(e).__name__ + ": " + str(e),
                           seconds=round(time.monotonic() - start, 3))
            stream.write(json.dumps(row) + "\n")
            stream.flush()
            print(case, round(row.get("log_value_per_K2", float("nan")), 5), flush=True)


if __name__ == "__main__":
    main()
