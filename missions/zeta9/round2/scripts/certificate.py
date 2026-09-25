"""Independent finite arithmetic certificates for the second zeta(9) round.

Pure standard library. Integer/Fraction operations certify divisibility; logs
are diagnostics only. This file does not evaluate zeta or select candidates.
Proofs are in ../research/arithmetic.md. Default CLI output is stdout.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from functools import reduce
import gzip
import hashlib
import json
import math
from pathlib import Path
import sys

sys.set_int_max_str_digits(0)


def validate(pole_order, n, m):
    if pole_order not in (3, 5, 7, 9):
        raise ValueError("pole_order must be 3, 5, 7, or 9")
    if n < 2 or n % 2 or m < 0:
        raise ValueError("require even n >= 2 and m >= 0")
    b = 10 - pole_order
    if 2 * b * m > pole_order * (n + 1) - 2:
        raise ValueError("rational function is outside the properness domain")


def primes_up_to(n):
    flags = bytearray(b"\1") * (n + 1)
    flags[:2] = b"\0\0"
    for p in range(2, math.isqrt(n) + 1):
        if flags[p]:
            flags[p * p:n + 1:p] = b"\0" * ((n - p * p) // p + 1)
    return [p for p in range(2, n + 1) if flags[p]]


def vp_factorial(n, prime):
    total = 0
    while n:
        n //= prime
        total += n
    return total


def vp_integer(n, prime):
    n = abs(n)
    if n == 0:
        raise ValueError("the certificate never requires v_p(0)")
    result = 0
    while n % prime == 0:
        n //= prime
        result += 1
    return result


def prime_power_count(n, prime):
    answer = 0
    while n >= prime:
        n //= prime
        answer += 1
    return answer


def highest_coefficients(pole_order, n, m):
    validate(pole_order, n, m)
    b = 10 - pole_order
    return [(-1) ** (m + j) * math.comb(n, j) ** pole_order
            * math.comb(j + m, m) ** b
            * math.comb(n - j + m, m) ** b for j in range(n + 1)]


def coefficient_valuation(pole_order, n, m, j, prime):
    b = 10 - pole_order
    return (pole_order * vp_factorial(n, prime)
            + b * vp_factorial(j + m, prime)
            + b * vp_factorial(n - j + m, prime)
            - 10 * vp_factorial(j, prime)
            - 10 * vp_factorial(n - j, prime)
            - 2 * b * vp_factorial(m, prime))


def rational_gcd(*values):
    """Positive generator of the integer span of nonzero rationals."""
    values = [abs(Fraction(x)) for x in values if x]
    if not values:
        return Fraction(0)
    return Fraction(reduce(math.gcd, (x.numerator for x in values)),
                    reduce(math.lcm, (x.denominator for x in values)))


def primitive_multiplier(vector):
    vector = list(map(Fraction, vector))
    if not any(vector):
        raise ValueError("zero vectors have no primitive multiplier")
    denominator = reduce(math.lcm, (v.denominator for v in vector), 1)
    coefficients = [int(denominator * v) for v in vector]
    content = reduce(math.gcd, coefficients)
    return Fraction(denominator, abs(content))


def finite_certificate(pole_order, n, m):
    """Return exact rational certificates and all supporting prime exponents."""
    validate(pole_order, n, m)
    b = 10 - pole_order
    common = abs(reduce(math.gcd, highest_coefficients(pole_order, n, m)))
    lcm_n = lcm_nm = 1
    rows = []
    factor_ratio = math.factorial(m) // math.factorial(n) if m > n else 1
    for prime in primes_up_to(n + m):
        e = prime_power_count(n + m, prime)
        f = prime_power_count(n, prime)
        lcm_nm *= prime ** e
        lcm_n *= prime ** f
        nu = min(coefficient_valuation(pole_order, n, m, j, prime)
                 for j in range(n + 1))
        assert nu == vp_integer(common, prime)
        large = None
        if prime * prime > n + m:
            large = b * int((n % prime) + 2 * (m % prime) >= 2 * prime - 1)
            assert nu == large
        split = (pole_order - 1) * e + b * f - nu
        simple = None
        if pole_order in (7, 9):
            simple = 9 * f + 2 * b * vp_integer(factor_ratio, prime)
        rows.append({"prime": prime, "G_valuation": nu,
                     "large_prime_formula": large,
                     "lcm_n_valuation": f, "lcm_n_plus_m_valuation": e,
                     "safe_valuation": 9 * e - nu,
                     "split_valuation": split,
                     "simple_or_extended_valuation": simple,
                     "combined_valuation": min(split, simple) if simple is not None else split})
    safe = Fraction(lcm_nm ** 9, common)
    split = Fraction(lcm_nm ** (pole_order - 1) * lcm_n ** b, common)
    certificates = {"safe": safe, "split": split}
    if pole_order in (7, 9):
        certificates["simple_or_extended"] = Fraction(factor_ratio ** (2 * b) * lcm_n ** 9)
    certificates["combined"] = rational_gcd(*certificates.values())
    via_primes = Fraction(1)
    for row in rows:
        exponent = row["combined_valuation"]
        via_primes *= Fraction(row["prime"] ** exponent) if exponent >= 0 else Fraction(1, row["prime"] ** (-exponent))
    assert via_primes == certificates["combined"]
    return {"pole_order": pole_order, "d": 9 - pole_order, "b": b,
            "n": n, "m": m, "G": common, "lcm_n": lcm_n,
            "lcm_n_plus_m": lcm_nm, "certificates": certificates,
            "prime_bounds": rows}


def audit_vector(certificate, vector):
    """Check complete exact vector, not only its top zeta coefficient."""
    vector = list(map(Fraction, vector))
    expected = (certificate["pole_order"] - 1) // 2 + 1
    if len(vector) != expected:
        raise ValueError("expected [B, A_(d+3), ..., A_9]")
    primitive = primitive_multiplier(vector)
    result = {"primitive_multiplier": primitive, "multipliers": {}}
    for name, multiplier in certificate["certificates"].items():
        scaled = [multiplier * value for value in vector]
        if not all(value.denominator == 1 for value in scaled):
            raise AssertionError(f"{name} did not integerize the whole vector")
        gap = multiplier / primitive
        assert gap.denominator == 1 and gap > 0
        result["multipliers"][name] = {
            "ratio_to_primitive": gap,
            "log_ratio_per_n": math.log(gap.numerator) / certificate["n"]}
    return result


def generalized_binomial(exponent, k):
    if exponent >= 0:
        return math.comb(exponent, k) if k <= exponent else 0
    return (-1) ** k * math.comb(k - exponent - 1, k)


def direct_taylor_pf(pole_order, n, m):
    """Independent, slower finite Taylor product for small verification cases."""
    C = highest_coefficients(pole_order, n, m)
    b = 10 - pole_order
    output = []
    for j in range(n + 1):
        factors = ([( -(j + a), b) for a in range(1, m + 1)]
                   + [(n - j + a, b) for a in range(1, m + 1)]
                   + [(-a, -pole_order) for a in range(1, j + 1)]
                   + [(a, -pole_order) for a in range(1, n - j + 1)])
        series = [Fraction(1)] + [Fraction(0)] * (pole_order - 1)
        for denominator, exponent in factors:
            term = [Fraction(generalized_binomial(exponent, h), denominator ** h)
                    for h in range(pole_order)]
            series = [sum((series[a] * term[h - a] for a in range(h + 1)), Fraction(0))
                      for h in range(pole_order)]
        output.append({pole_order - h: C[j] * series[h]
                       for h in range(pole_order)})
    return output


def vector_from_pf(pole_order, n, m, pf):
    d = 9 - pole_order
    harmonics = {s: [Fraction(0)] for s in range(1, 10)}
    for s in harmonics:
        for j in range(1, n + 1):
            harmonics[s].append(harmonics[s][-1] + Fraction(1, j ** s))
    totals = {k: sum((pf[j][k] for j in range(n + 1)), Fraction(0))
              for k in range(1, pole_order + 1)}
    assert totals[1] == 0
    assert all(totals[k] == 0 for k in range(2, pole_order + 1, 2))
    for j in range(n + 1):
        for k in range(1, pole_order + 1):
            assert pf[n - j][k] == (-1) ** (k + 1) * pf[j][k]
    constant = -sum((math.comb(d + k - 1, d) * pf[j][k] * harmonics[d + k][j]
                     for j in range(n + 1) for k in range(1, pole_order + 1)), Fraction(0))
    zeta_coefficients = [math.comb(d + k - 1, d) * totals[k]
                         for k in range(3, pole_order + 1, 2)]
    return [constant, *zeta_coefficients]


def self_test():
    floor_cases = 0
    for pole_order in (3, 5, 7, 9):
        b = 10 - pole_order
        for n in (2, 4, 6, 8, 10, 12):
            for m in range((pole_order * (n + 1) - 2) // (2 * b) + 1):
                finite_certificate(pole_order, n, m)
                floor_cases += 1
    cases = [(3, 6, 1), (5, 4, 2), (7, 4, 0), (7, 4, 3),
             (7, 4, 4), (7, 4, 5), (9, 4, 3), (9, 4, 4),
             (9, 4, 5), (9, 4, 17)]
    for pole_order, n, m in cases:
        certificate = finite_certificate(pole_order, n, m)
        pf = direct_taylor_pf(pole_order, n, m)
        D, E, common = certificate["lcm_n_plus_m"], certificate["lcm_n"], certificate["G"]
        extra = (math.factorial(m) // math.factorial(n)) ** (2 * (10 - pole_order)) if m > n else 1
        for row in pf:
            for k, value in row.items():
                assert (Fraction(D ** (pole_order - k), common) * value).denominator == 1
                if pole_order in (7, 9):
                    assert (extra * E ** (pole_order - k) * value).denominator == 1
        vector = vector_from_pf(pole_order, n, m, pf)
        audit_vector(certificate, vector)
    return {"floor_and_large_prime_cases": floor_cases,
            "independent_direct_taylor_cases": len(cases), "passed": True}


def audit_index(index_path):
    """Read frozen exact artifacts; verify every coordinate independently."""
    raw_index = index_path.read_bytes()
    records = [json.loads(line) for line in raw_index.decode("utf-8").splitlines() if line.strip()]
    results = []
    counts = {}
    for row in records:
        artifact_path = Path(row["artifact_path"])
        raw_artifact = artifact_path.read_bytes()
        digest = hashlib.sha256(raw_artifact).hexdigest()
        assert digest == row["artifact_sha256"]
        data = json.loads(gzip.decompress(raw_artifact).decode("utf-8"))
        cert = finite_certificate(row["p"], row["n"], row["m"])
        assert cert["G"] == int(data["G_residue_gcd"])
        vector = [Fraction(int(a), int(b)) for a, b in data["raw_rational_vector"]]
        audit = audit_vector(cert, vector)
        assert audit["primitive_multiplier"] == Fraction(*map(int, data["primitive_multiplier"]))
        assert cert["certificates"]["safe"] == Fraction(*map(int, data["certificate_multiplier"]))
        counts[row["p"]] = counts.get(row["p"], 0) + 1
        results.append({
            "case_id": row["case_id"], "pole_order": row["p"], "n": row["n"], "m": row["m"],
            "artifact_path": str(artifact_path), "artifact_sha256": digest,
            "G": cert["G"], "certificates": cert["certificates"], "audit": audit,
            "local_columns": ["prime", "G_valuation", "lcm_n_valuation", "lcm_n_plus_m_valuation", "combined_valuation"],
            "local_certificate": [[r["prime"], r["G_valuation"], r["lcm_n_valuation"],
                                   r["lcm_n_plus_m_valuation"], r["combined_valuation"]]
                                  for r in cert["prime_bounds"]],
            "passed": True})
    return {"status": "passed", "proof": "missions/zeta9/round2/research/arithmetic.md",
            "index_path": str(index_path), "index_sha256": hashlib.sha256(raw_index).hexdigest(),
            "certificate_script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "self_test": self_test(), "atom_count": len(records), "by_pole_order": counts,
            "checks": ["artifact hashes", "highest-residue gcd", "all-prime floor minimum",
                       "large-prime closed formula", "safe multiplier agrees with exact artifact",
                       "every coefficient integerized by every certificate",
                       "primitive multiplier agrees with exact artifact",
                       "every certificate/primitive ratio is a positive integer"],
            "logs_are_floating_diagnostics": True, "cases": results}


def json_ready(value):
    if isinstance(value, Fraction):
        return [str(value.numerator), str(value.denominator)]
    if isinstance(value, int):
        return str(value) if abs(value) > 2 ** 53 else value
    if isinstance(value, dict):
        return {key: json_ready(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_ready(item) for item in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pole-order", type=int)
    parser.add_argument("--n", type=int)
    parser.add_argument("--m", type=int)
    parser.add_argument("--vector", type=Path,
                        help="JSON or .gz list/object with raw_rational_vector or rational_vector")
    parser.add_argument("--audit-index", type=Path, help="read-only exact atom index comparison")
    parser.add_argument("--output", type=Path, help="write this arithmetic audit JSON; otherwise stdout")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        answer = self_test()
    elif args.audit_index:
        answer = audit_index(args.audit_index)
    else:
        if None in (args.pole_order, args.n, args.m):
            parser.error("supply --pole-order, --n, --m, or --self-test")
        answer = finite_certificate(args.pole_order, args.n, args.m)
        if args.vector:
            raw = args.vector.read_bytes()
            if args.vector.suffix == ".gz":
                raw = gzip.decompress(raw)
            data = json.loads(raw.decode("utf-8"))
            vector = data.get("raw_rational_vector", data.get("rational_vector")) if isinstance(data, dict) else data
            answer["audit"] = audit_vector(answer, [Fraction(int(a), int(b)) for a, b in vector])
    rendered = json.dumps(json_ready(answer), ensure_ascii=False, indent=2)
    if args.output:
        args.output.write_text(rendered + "\n", encoding="utf-8")
        print(json.dumps({"output": str(args.output), "status": answer.get("status"),
                          "atom_count": answer.get("atom_count"), "self_test": answer.get("self_test")}))
    else:
        print(rendered)


if __name__ == "__main__":
    main()
