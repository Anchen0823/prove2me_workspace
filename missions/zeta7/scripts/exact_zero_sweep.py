"""Exact finite search over nonuniform and nonprefix squared zero factors."""
from __future__ import annotations

import json
import time

from exact_hankel import ROOT, evaluate, parameters, record


PATTERNS = {
    "two_cutoffs_1_2": {1: 2, 2: 1},
    "reverse_1_2": {1: 1, 2: 2},
    "skip_first_2": {2: 2},
    "skip_first_3": {3: 2},
    "gapped_1_3": {1: 1, 3: 1},
    "gapped_2_3": {2: 1, 3: 1},
    "mixed_1_3": {1: 2, 3: 1},
    "prefix_3": {1: 1, 2: 1, 3: 1},
}


def main():
    out = ROOT / "missions/zeta7/verification/exact_zero_sweep.jsonl"
    with out.open("w", encoding="utf-8") as stream:
        for K in (8, 12, 16):
            for name, zeros in PATTERNS.items():
                r = K - len(zeros)
                for factor in (.6, .8, 1):
                    h = max(1, round(r * factor))
                    start = time.monotonic()
                    try:
                        result = parameters(7, K, 0, 0, h, zeros)
                        row = record(result, evaluate(result), False)
                        row["pattern"] = name
                        row["seconds"] = round(time.monotonic() - start, 3)
                    except Exception as e:
                        row = dict(s=7, K=K, h=h, pattern=name,
                                   error=type(e).__name__ + ": " + str(e),
                                   seconds=round(time.monotonic() - start, 3))
                    stream.write(json.dumps(row) + "\n")
                    stream.flush()
                    print(K, name, h, round(row.get("log_value_per_K2", float("nan")), 6), flush=True)


if __name__ == "__main__":
    main()
