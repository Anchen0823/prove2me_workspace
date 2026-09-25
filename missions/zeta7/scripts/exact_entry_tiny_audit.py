"""Independently compare finite entry certificates with exact determinant coefficients."""
from __future__ import annotations

from fractions import Fraction
import json
import math
import sys

from exact_hankel import ROOT, parameters
from round2_entry_certificate import certify


def direct_fraction(value):
    return Fraction(int(value.numer()), int(value.denom()))


def check(case_id, s, K, zeros, exponents):
    h = len(exponents)
    result = parameters(s, K, 0, 0, h, zeros, exponents)
    row = dict(case_id=case_id, s=s, K=K, h=h,
               zero_multiplicities={str(j): m for j, m in zeros.items()},
               exponents=exponents,
               primitive_coefficients_ascending=result["coeffs"])
    certificate = certify(row)
    multiplier = Fraction(certificate["multiplier_numerator"],
                          certificate["multiplier_denominator"])
    scale = direct_fraction(result["primitive_scale"])
    gap = certificate["gap_integer"]
    assert multiplier / scale == gap and gap >= 1
    scaled = [multiplier * direct_fraction(result["delta"][i])
              for i in range(result["degree"] + 1)]
    assert all(x.denominator == 1 for x in scaled)
    assert [int(x) for x in scaled] == [gap * c for c in result["coeffs"]]
    assert math.gcd(*(int(x) for x in scaled)) == gap
    assert all(item["actual_minimum"] >= item["lower_bound"]
               for item in certificate["local"])
    return dict(case_id=case_id, s=s, K=K, h=h, zeros=row["zero_multiplicities"],
                exponents=exponents, degree=result["degree"], B_rank=result["B_rank"],
                prime_limit=certificate["prime_limit"],
                certified_multiplier_numerator=multiplier.numerator,
                certified_multiplier_denominator=multiplier.denominator,
                primitive_scale_numerator=scale.numerator,
                primitive_scale_denominator=scale.denominator,
                exact_integer_gap=gap, gap_log_per_K2=certificate["gap_log_per_K2"],
                direct_coefficient_identity=True, all_primes_integral=True,
                local_bounds_checked=len(certificate["local"]))


def main():
    cases = [
        ("s5-uniform", 5, 7, {1: 2}, [0, 1, 2]),
        ("s7-layered", 7, 8, {1: 2, 2: 1}, [0, 1, 2, 3]),
        ("s7-shift", 7, 8, {1: 2}, [1, 2, 3]),
        ("s9-uniform", 9, 7, {1: 1}, [0, 1, 2]),
    ]
    rows = [check(*case) for case in cases]
    out = ROOT / "missions/zeta7/verification/round2-entry-tiny-audit.json"
    out.write_text(json.dumps(rows, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"{len(rows)} tiny full-prime coefficient identities passed: {out}")


if __name__ == "__main__":
    main()
