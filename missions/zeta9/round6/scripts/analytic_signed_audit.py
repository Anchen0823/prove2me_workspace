"""Exact signed finite-sum intervals for the two Gauss directions.

Reads analytic-triangle-exact-n*.json.gz; never uses zeta(9) numerics.
"""

from __future__ import annotations

from fractions import Fraction
import gzip
import hashlib
import json
from pathlib import Path
import sys

sys.set_int_max_str_digits(0)
VERIFY = Path(__file__).resolve().parents[1] / "verification"


def frac(pair: list[str]) -> Fraction:
    return Fraction(int(pair[0]), int(pair[1]))


def pair(x: Fraction) -> list[str]:
    return [str(x.numerator), str(x.denominator)]


def summary(x: Fraction) -> dict:
    string = f"{x.numerator}/{x.denominator}"
    return {
        "sign": (x > 0) - (x < 0),
        "numerator_digits": len(str(abs(x.numerator))),
        "denominator_digits": len(str(x.denominator)),
        "sha256": hashlib.sha256(string.encode()).hexdigest(),
    }


def audit_one(path: Path) -> tuple[dict, dict]:
    with gzip.open(path, "rt", encoding="utf-8") as stream:
        data = json.load(stream)
    n = data["n"]
    T = [[frac(x) for x in row] for row in data["inverse_output_T_rows"]]
    lows = [frac(item["lower"]) for item in data["moments"]]
    tails = [frac(item["tail"]) for item in data["moments"]]
    gauss = next(item for item in data["gram_and_gauss"] if item["weights"] == "upper")
    g1 = tuple(gauss["gauss_g1"])
    g2 = tuple(gauss["gauss_g2"])
    if abs(g1[0]*g2[1] - g1[1]*g2[0]) != 1:
        raise AssertionError("two Gauss directions not unimodular")
    rows, exact_rows = [], []
    for label, z in (("g1", g1), ("g2", g2)):
        W = [row[0]*z[0] + row[1]*z[1] for row in T]
        center = sum((w*s for w,s in zip(W,lows)), Fraction())
        radius = sum((abs(w)*t for w,t in zip(W,tails)), Fraction())
        if radius < 0:
            raise AssertionError("negative tail radius")
        interval = (center-radius, center+radius)
        sign = 1 if interval[0] > 0 else (-1 if interval[1] < 0 else 0)
        rows.append({
            "n": n, "direction": label, "output_B_A9": z,
            "strict_nonzero": sign != 0, "raw_L_sign": sign,
            "center": summary(center), "tail_radius": summary(radius),
            "lower": summary(interval[0]), "upper": summary(interval[1]),
        })
        exact_rows.append({
            "direction": label, "output_B_A9": z,
            "W_rational": [pair(x) for x in W],
            "center": pair(center), "radius": pair(radius),
            "lower": pair(interval[0]), "upper": pair(interval[1]),
        })
    return (
        {"n": n, "source": path.name, "det_abs": 1, "rows": rows},
        {"n": n, "source": path.name, "rows": exact_rows},
    )


def main() -> None:
    summaries, exact = [], []
    for n in (12, 24, 48, 96):
        path = VERIFY / f"analytic-triangle-exact-n{n}.json.gz"
        a, b = audit_one(path)
        summaries.append(a)
        exact.append(b)
    output = {
        "status": "exact_rational_signed_intervals",
        "no_zeta9_numerical_input": True,
        "cases": len(summaries),
        "directions": 2*len(summaries),
        "all_eight_strictly_nonzero": all(
            row["strict_nonzero"] for item in summaries for row in item["rows"]
        ),
        "rows": summaries,
    }
    (VERIFY / "analytic-signed.json").write_text(
        json.dumps(output, indent=2), encoding="utf-8"
    )
    with gzip.open(VERIFY / "analytic-signed-exact.json.gz", "wt", encoding="utf-8") as stream:
        json.dump(exact, stream, separators=(",", ":"))
    print(f"all eight strictly nonzero: {output['all_eight_strictly_nonzero']}")
    for item in summaries:
        print(item["n"], [(r["direction"], r["raw_L_sign"]) for r in item["rows"]])


if __name__ == "__main__":
    main()
