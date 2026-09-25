"""Exact Hankel polynomial experiment for the odd-zeta positive functional.

Run with the bundled Python and PYTHONPATH=tmp/zeta7/exact_packages.
This script is evidence from finite calculations, not an irrationality proof.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import math
from pathlib import Path
import sys
import time

sys.set_int_max_str_digits(0)

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "tmp/zeta7/exact_packages"))

from flint import arb, ctx, fmpq, fmpq_mat, fmpq_poly, fmpz  # type: ignore
import mpmath as mp  # type: ignore


def moment(s: int, e: int) -> fmpq:
    value = fmpq.bernoulli(2 * e + 2)
    ratio = math.factorial(2 * e + s) // math.factorial(2 * e + 2)
    return (-1 if e & 1 else 1) * value * ratio / math.factorial(s - 1)


def rational_to_mp(value: fmpq):
    return mp.mpf(str(value.numer())) / mp.mpf(str(value.denom()))


def parameters(s: int, K: int, N: int, q: int, h: int | None = None,
               zero_multiplicities: dict[int, int] | None = None,
               exponents: list[int] | tuple[int, ...] | None = None):
    if s < 3 or s % 2 != 1 or K <= N or N < 0 or (q < 1 and zero_multiplicities is None):
        raise ValueError("Require odd s>=3, 0<=N<K, q>=1 unless zeros are supplied")
    zeros = ({j: q for j in range(1, N + 1)} if zero_multiplicities is None
             else dict(zero_multiplicities))
    if any(j < 1 or j > K or m < 1 for j, m in zeros.items()) or len(zeros) >= K:
        raise ValueError("Zero factors must have positive multiplicity at distinct 1<=j<=K")
    pole_count = K - len(zeros)
    if h is None:
        h = pole_count if exponents is None else len(exponents)
    if h < 1:
        raise ValueError("Require h>=1")
    if exponents is None:
        exponents = tuple(range(h))
    else:
        exponents = tuple(exponents)
        if len(exponents) != h or any(type(e) is not int or e < 0 for e in exponents):
            raise ValueError("Exponents must be nonnegative integers of length h")
        if any(a >= b for a, b in zip(exponents, exponents[1:])):
            raise ValueError("Exponents must be strictly increasing")
    t = fmpq_poly([0, 1])
    pbase = fmpq_poly([1])
    tail = fmpq_poly([1])
    for j in range(1, K + 1):
        if j in zeros:
            pbase *= (t + j * j) ** (2 * zeros[j] - 1)
        else:
            tail *= t + j * j
    quotient, remainder = divmod(pbase, tail)
    deriv = tail.derivative()
    poles = []
    harmonic = fmpq(0)
    for j in range(1, K + 1):
        harmonic += fmpq(1, j ** s)
        if j not in zeros:
            a = -j * j
            residue = pbase(a) / deriv(a)
            const = -j ** (s - 1) * harmonic - fmpq(1, s - 1) + fmpq(1, 2 * j)
            poles.append((a, residue, fmpq(j ** (s - 1)), const))
    # Verify partial fractions exactly at t=0 and t=1.
    for x in (0, 1):
        lhs = pbase(x) / tail(x)
        rhs = quotient(x) + sum((r / (x - a) for a, r, _, _ in poles), fmpq(0))
        if lhs != rhs:
            raise AssertionError("partial fraction check failed")
    max_e = 2 * exponents[-1]
    max_moment = max(0, quotient.degree() + max_e)
    mu = [moment(s, e) for e in range(max_moment + 1)]
    avals, bvals = [], []
    powers = [fmpq(1)] * pole_count
    for e in range(max_e + 1):
        polynomial_value = sum((co * mu[i] for i, co in enumerate(quotient)), fmpq(0))
        a = polynomial_value + sum((r * powers[k] * c for k, (_, r, _, c) in enumerate(poles)), fmpq(0))
        b = sum((r * powers[k] * x for k, (_, r, x, _) in enumerate(poles)), fmpq(0))
        avals.append(a)
        bvals.append(b)
        residue_sum = sum((r * powers[k] for k, (_, r, _, _) in enumerate(poles)), fmpq(0))
        quotient = quotient * t + residue_sum
        powers = [powers[k] * pole[0] for k, pole in enumerate(poles)]
    A = fmpq_mat([[avals[exponents[i] + exponents[j]] for j in range(h)] for i in range(h)])
    B = fmpq_mat([[bvals[exponents[i] + exponents[j]] for j in range(h)] for i in range(h)])
    b_rank = B.rank()
    if b_rank > min(h, pole_count):
        raise AssertionError("X coefficient rank exceeds pole count")
    contiguous = exponents == tuple(range(exponents[0], exponents[0] + h))
    infinity_threshold_L = None
    predicted_b_rank = None
    if contiguous:
        g = exponents[0]
        d = 2 * sum(zeros.values())
        infinity_threshold_L = K - d - (s + 1) // 2 - 2 * g
        boundary_coefficient = (-1) ** ((s - 1) // 2)
        for i in range(h):
            for j in range(h):
                if i + j < infinity_threshold_L and B[i, j] != 0:
                    raise AssertionError("X coefficient violates infinity zero triangle")
                if i + j == infinity_threshold_L and B[i, j] != boundary_coefficient:
                    raise AssertionError("X coefficient violates infinity anti-diagonal")
        if infinity_threshold_L > 2 * h - 2:
            predicted_b_rank = 0
        elif h - 1 <= infinity_threshold_L <= 2 * h - 2:
            predicted_b_rank = 2 * h - 1 - infinity_threshold_L
        if predicted_b_rank is not None and predicted_b_rank != b_rank:
            raise AssertionError("X coefficient rank violates infinity prediction")
    degree_bound = b_rank
    if b_rank == h:
        delta = B.det() * (-B.inv() * A).charpoly()
    else:
        # Newton forward differences at X=0,...,degree_bound. Every
        # determinant is exact in Q; degree <= rank(B) <= pole_count.
        diffs = [(A + x * B).det() for x in range(degree_bound + 1)]
        delta = fmpq_poly([0])
        binomial = fmpq_poly([1])
        for k in range(degree_bound + 1):
            delta += diffs[0] * binomial
            diffs = [diffs[i + 1] - diffs[i] for i in range(len(diffs) - 1)]
            binomial = binomial * (t - k) / (k + 1)
    if delta.degree() != b_rank:
        raise AssertionError("determinant degree does not equal X coefficient rank")
    denominator = int(delta.denom())
    numerator = delta.numer()
    content = int(numerator.content())
    coeffs = [int(numerator[i]) // content for i in range(delta.degree() + 1)]
    if h <= 12:
        for x in (0, 1, degree_bound + 1):
            if delta(x) != (A + x * B).det():
                raise AssertionError("characteristic-polynomial determinant check failed")
    return dict(s=s, K=K, N=N, q=q, h=h, exponents=list(exponents),
                degree=delta.degree(), B_rank=b_rank,
                infinity_threshold_L=infinity_threshold_L,
                predicted_B_rank=predicted_b_rank, coeffs=coeffs,
                zero_multiplicities={str(j): m for j, m in sorted(zeros.items())},
                denominator=denominator, numerator_content=content,
                primitive_scale=fmpq(denominator, content),
                delta=delta, A=A, B=B)


def ball_interval(value: arb, digits: int = 30):
    mid, rad, exponent = value.mid_rad_10exp(digits)
    return dict(mid=str(mid), rad=str(rad), exp=int(exponent))


def evaluate(result: dict, extra_digits: int = 40):
    coeffs = result["coeffs"]
    height_digits = max(len(str(abs(c))) for c in coeffs if c)
    # Arb guarantees ζ(s), every Horner operation, and logarithms are
    # enclosed. Raise precision until the entire value interval is positive
    # and its relative accuracy exceeds 80 bits.
    bits = max(256, int(3.4 * (height_digits + extra_digits)))
    for _ in range(5):
        with ctx.workprec(bits):
            z = arb(result["s"]).zeta()
            v = arb(0)
            for c in reversed(coeffs):
                v = v * z + fmpz(c)
            if v.lower() > 0 and v.rel_accuracy_bits() >= 80:
                logv = v.log()
                log10v = logv / arb(10).log()
                return dict(log10_value=mp.nstr(float(log10v), 17),
                            log_value=mp.nstr(float(logv), 17),
                            arb_bits=bits, relative_accuracy_bits=v.rel_accuracy_bits(),
                            positive=True, P_interval=ball_interval(v),
                            log_interval=ball_interval(logv),
                            log10_interval=ball_interval(log10v))
        bits *= 2
    raise ArithmeticError("Arb Horner interval did not certify positivity to 80 bits")


def record(result: dict, eval_result: dict, include_coefficients: bool):
    coeffs = result["coeffs"]
    text = ",".join(str(c) for c in coeffs)
    ans = {k: result[k] for k in ("s", "K", "N", "q", "h", "degree", "denominator", "numerator_content")}
    ans["zero_multiplicities"] = result["zero_multiplicities"]
    ans["exponents"] = result["exponents"]
    ans["B_rank"] = result["B_rank"]
    ans["infinity_threshold_L"] = result["infinity_threshold_L"]
    ans["predicted_B_rank"] = result["predicted_B_rank"]
    ans["primitive_scale_numerator"] = int(result["primitive_scale"].numer())
    ans["primitive_scale_denominator"] = int(result["primitive_scale"].denom())
    ans.update(eval_result)
    ans["log_value_per_K2"] = float(eval_result["log_value"]) / result["K"] ** 2
    ans["height_digits"] = max(len(str(abs(c))) for c in coeffs if c)
    ans["coefficients_sha256"] = hashlib.sha256(text.encode()).hexdigest()
    if include_coefficients:
        ans["primitive_coefficients_ascending"] = coeffs
    return ans


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cases", default="5:8:1:3,5:12:1:3,7:8:1:3,7:12:1:3")
    parser.add_argument("--output", default="missions/zeta7/verification/exact_results.json")
    parser.add_argument("--coefficients", action="store_true", help="save full primitive coefficients")
    args = parser.parse_args()
    cases = []
    for case in args.cases.split(","):
        cases.append(tuple(int(x) for x in case.split(":")))
    records = []
    for case in cases:
        start = time.monotonic()
        result = parameters(*case)
        evaluation = evaluate(result)
        row = record(result, evaluation, args.coefficients)
        row["seconds"] = round(time.monotonic() - start, 3)
        print(json.dumps(row, ensure_ascii=False), flush=True)
        records.append(row)
    output = ROOT / args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    if output.suffix == ".gz":
        with gzip.open(output, "wt", encoding="utf-8") as stream:
            json.dump(records, stream, ensure_ascii=False, indent=2)
    else:
        output.write_text(json.dumps(records, ensure_ascii=False, indent=2), encoding="utf-8")


if __name__ == "__main__":
    main()
