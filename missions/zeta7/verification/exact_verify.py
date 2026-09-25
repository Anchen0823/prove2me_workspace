"""Check saved exact coefficient and Arb interval certificates."""
from __future__ import annotations

import gzip
import hashlib
import json
import math
from pathlib import Path
import sys

sys.set_int_max_str_digits(0)
BASE = Path(__file__).resolve().parent
JSONL = ("exact_sweep.jsonl", "exact_h_sweep.jsonl",
         "exact_h_large.jsonl", "exact_zero_sweep.jsonl")
GZIP = ("exact_baseline.json.gz", "exact_K80.json.gz", "exact_K80_s5.json.gz")


def positive(interval):
    return int(interval["mid"]) - int(interval["rad"]) > 0


def negative(interval):
    return int(interval["mid"]) + int(interval["rad"]) < 0


def check(row):
    assert "error" not in row
    assert row["positive"] and row["relative_accuracy_bits"] >= 80
    assert positive(row["P_interval"])
    if row["s"] == 7:
        assert positive(row["log_interval"])  # proves finite P(zeta(7))>1
    elif row["s"] == 5:
        assert negative(row["log_interval"])  # proves finite 0<P(zeta(5))<1
    coeffs = row.get("primitive_coefficients_ascending")
    if coeffs is not None:
        assert len(coeffs) == row["degree"] + 1
        assert math.gcd(*coeffs) == 1
        encoded = ",".join(str(c) for c in coeffs).encode()
        assert hashlib.sha256(encoded).hexdigest() == row["coefficients_sha256"]


def main():
    count = 0
    for name in JSONL:
        rows = [json.loads(line) for line in (BASE / name).read_text(encoding="utf-8").splitlines()]
        for row in rows:
            check(row)
        print(name, len(rows), "verified")
        count += len(rows)
    for name in GZIP:
        with gzip.open(BASE / name, "rt", encoding="utf-8") as stream:
            rows = json.load(stream)
        for row in rows:
            check(row)
            assert "primitive_coefficients_ascending" in row
        print(name, len(rows), "verified with complete primitive coefficients")
        count += len(rows)
    print("Total:", count, "saved certificates checked")


if __name__ == "__main__":
    main()
