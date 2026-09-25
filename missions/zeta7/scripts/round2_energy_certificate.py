"""Global Arb certificate for one explicit 32-arc comparison measure.

The arcs come from a floating-point exploratory run, but every saved decimal
endpoint is thereafter an exact rational. This proves an upper bound for that
explicit measure only; it does not prove zeta(7) irrationality.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "tmp/zeta7/exact_packages"))
from flint import arb, ctx, fmpq

SOURCE = ROOT / "missions/zeta7/verification/round2-energy.json"
OUTPUT = ROOT / "missions/zeta7/verification/round2-energy-certificate.json"
BITS = 192
TARGET = Fraction(-153, 25)
EPS = Fraction(1, 10**14)
TAIL_T = Fraction(2)
LAM = Fraction(1, 2)
GAMMA = Fraction(1, 40)
LAYERS = ((Fraction(3, 40), 1), (Fraction(3, 20), 3))


def q(value: Fraction):
    return fmpq(value.numerator, value.denominator)


def a(value: Fraction):
    return arb(q(value))


def interval(lo: Fraction, hi: Fraction):
    return a(lo).union(a(hi))


def serial(value, digits=45):
    mid, rad, exp = value.mid_rad_10exp(digits)
    return dict(mid=str(mid), rad=str(rad), exp=int(exp))


def rational_json(value: Fraction):
    return dict(numerator=str(value.numerator), denominator=str(value.denominator))


def parse_rational(value):
    return Fraction(int(value["numerator"]), int(value["denominator"]))


def ball_upper_rational(value):
    magnitude = Fraction(int(value["mid"]) + int(value["rad"]))
    exponent = int(value["exp"])
    return magnitude * (10**exponent if exponent >= 0 else Fraction(1, 10**(-exponent)))


def raw_measure():
    data = json.loads(SOURCE.read_text(encoding="utf-8"))
    matches = [r for r in data if r.get("layers") == [[0.075, 1], [0.15, 3]]
               and r.get("lam") == 0.5 and r.get("gamma") == 0.025
               and r.get("arcs") == 32]
    if not matches:
        raise ValueError("Requested 32-arc exploratory measure not found")
    source = matches[0]
    left = [Fraction(repr(v)) for v in source["a"]]
    right = [Fraction(repr(v)) for v in source["b"]]
    raw_weights = [Fraction(repr(v)) for v in source["c"]]
    if not (len(left) == len(right) == len(raw_weights) == 32):
        raise AssertionError("Expected exactly 32 arcs")
    weight_sum = sum(raw_weights)
    weights = [LAM * c / weight_sum for c in raw_weights]
    if not all(c > 0 for c in weights) or sum(weights) != LAM:
        raise AssertionError("Weights are not positive or not normalized")
    if not all(EPS < x < y < TAIL_T for x, y in zip(left, right)):
        raise AssertionError("Arc endpoint outside middle interval")
    if not all(left[i] > left[i + 1] and right[i] < right[i + 1]
               for i in range(31)):
        raise AssertionError("Arcs are not nested")
    return left, right, weights, source["case_id"]


def J(alpha: Fraction, t):
    if alpha == 0:
        return arb(0)
    z = t.sqrt()
    aa = a(alpha)
    return aa * (t + aa * aa).log() - 2 * aa + 2 * z * (aa / z).atan()


def field(t):
    value = 2 * arb.pi() * t.sqrt() + J(Fraction(1), t)
    for alpha, multiplicity in LAYERS:
        value -= 2 * multiplicity * J(alpha, t)
    return value - 2 * a(GAMMA) * t.log()


def field_prime(t):
    z = t.sqrt()
    value = (arb.pi() + (1 / z).atan()) / z
    for alpha, multiplicity in LAYERS:
        value -= 2 * multiplicity * (a(alpha) / z).atan() / z
    return value - 2 * a(GAMMA) / t


def arc_potential(t: Fraction, left: Fraction, right: Fraction):
    if left <= t <= right:
        return ((a(right - left)) / 4).log()
    center = (left + right) / 2
    if t < left:
        radical = a((left - t) * (right - t)).sqrt()
        return ((a(center - t) + radical) / 2).log()
    radical = a((t - left) * (t - right)).sqrt()
    return ((a(t - center) + radical) / 2).log()


def arc_derivative(lo: Fraction, hi: Fraction, left: Fraction, right: Fraction):
    if left <= lo and hi <= right:
        return arb(0)
    t = interval(lo, hi)
    if hi < left:
        return -1 / ((a(left) - t) * (a(right) - t)).sqrt()
    if lo > right:
        return 1 / ((t - a(left)) * (t - a(right))).sqrt()
    return None  # derivative is unbounded at a touched support endpoint


def gap_point(t: Fraction, arcs):
    potential = arb(0)
    for left, right, weight in arcs:
        potential += 2 * a(weight) * arc_potential(t, left, right)
    return potential - field(a(t))


def upper_middle(lo: Fraction, hi: Fraction, arcs):
    t = interval(lo, hi)
    if t.lower() <= 0:
        return None
    potential_upper = arb(0)
    for left, right, weight in arcs:
        p_lo = arc_potential(lo, left, right)
        p_hi = arc_potential(hi, left, right)
        endpoint_max = (p_lo + p_hi + abs(p_lo - p_hi)) / 2
        potential_upper += 2 * a(weight) * endpoint_max
    natural = potential_upper - field(t)
    # On endpoint-free intervals a mean-value upper bound usually costs much
    # less than natural interval subtraction. Both are valid independently.
    derivative = -field_prime(t)
    for left, right, weight in arcs:
        piece = arc_derivative(lo, hi, left, right)
        if piece is None:
            derivative = None
            break
        derivative += 2 * a(weight) * piece
    if derivative is None:
        return natural, "endpoint"
    midpoint = (lo + hi) / 2
    mean_value = gap_point(midpoint, arcs) + abs(derivative) * a((hi - lo) / 2)
    return ((mean_value, "derivative") if float(mean_value.upper()) < float(natural.upper())
            else (natural, "endpoint"))


def small_tail(arcs):
    b_max = max(right for _, right, _ in arcs)
    value = 2 * a(LAM) * a(b_max).log() + 2
    for alpha, multiplicity in LAYERS:
        value += 2 * multiplicity * J(alpha, a(EPS))
    value += 2 * a(GAMMA) * a(EPS).log()
    return value


def large_tail():
    sum_qa = sum(qi * alpha for alpha, qi in LAYERS)
    D = 2 * LAM - 1 + 2 * sum_qa + 2 * GAMMA
    C = 2 * sum(qi * alpha**3 for alpha, qi in LAYERS)
    if not (arb.pi() * a(TAIL_T).sqrt()).lower() > a(max(D, Fraction(0))):
        raise AssertionError("Large-tail bound is not decreasing from T")
    value = a(D) * a(TAIL_T).log() - 2 * arb.pi() * a(TAIL_T).sqrt() + a(C / TAIL_T)
    return value, D, C


def energy_and_constant(arcs):
    cumulative = Fraction(0)
    energy = arb(0)
    for left, right, weight in arcs:
        previous = cumulative
        cumulative += weight
        energy += a(cumulative**2 - previous**2) * a((right - left) / 4).log()
    if cumulative != LAM:
        raise AssertionError("Mass drift")
    linear = -2 * a(LAM)
    for alpha, multiplicity in LAYERS:
        linear += 4 * a(LAM) * multiplicity * a(alpha) * (1 - a(alpha).log())
    def F(v: Fraction):
        return 3 * a(v*v) - 2 * a(v*v) * a(2*v).log()
    cstar = linear + F(GAMMA + LAM) - F(GAMMA)
    U = cstar + a(LAM) * a(TARGET) - energy
    return energy, cstar, U


def certify(max_seconds: int):
    started = time.monotonic()
    with ctx.workprec(BITS):
        left, right, weights, source_id = raw_measure()
        arcs = list(zip(left, right, weights))
        small = small_tail(arcs)
        large, D, C = large_tail()
        if not (small.upper() < a(TARGET) and large.upper() < a(TARGET)):
            raise AssertionError("A tail upper bound exceeds target M")
        endpoints = sorted(set([EPS, TAIL_T, *left, *right]))
        pending = [(x, y) for x, y in zip(endpoints, endpoints[1:])]
        accepted = []
        target = a(TARGET)
        while pending:
            if time.monotonic() - started > max_seconds:
                raise TimeoutError("Global middle partition exceeded time cap")
            lo, hi = pending.pop()
            bound = upper_middle(lo, hi, arcs)
            if bound is not None and bound[0].upper() < target:
                accepted.append(dict(lo=rational_json(lo), hi=rational_json(hi),
                                     upper=serial(bound[0]), method=bound[1]))
                continue
            midpoint = (lo + hi) / 2
            if midpoint in (lo, hi) or len(accepted) + len(pending) > 100000:
                raise RuntimeError("Adaptive partition stalled")
            pending.extend(((lo, midpoint), (midpoint, hi)))
            if len(accepted) and len(accepted) % 500 == 0:
                print(f"accepted={len(accepted)} pending={len(pending)}", flush=True)
        energy, cstar, U = energy_and_constant(arcs)
        if not U.upper() < a(Fraction(507, 1000)):
            raise AssertionError("Certified U did not reach 0.507")
        result = dict(certified=True, scope="global real-energy upper bound only",
                      source_case_id=source_id,
                      source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
                      script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                      precision_bits=BITS, lambda_mass=rational_json(LAM),
                      gamma=rational_json(GAMMA),
                      layers=[dict(alpha=rational_json(alpha), q=qv) for alpha, qv in LAYERS],
                      arcs=[dict(left=rational_json(l), right=rational_json(r),
                                 weight=rational_json(w)) for l, r, w in arcs],
                      epsilon=rational_json(EPS), T=rational_json(TAIL_T),
                      target_M=rational_json(TARGET),
                      small_tail_upper=serial(small), large_tail_upper=serial(large),
                      large_tail_D=rational_json(D), large_tail_C=rational_json(C),
                      middle_intervals=accepted,
                      middle_interval_count=len(accepted),
                      energy_I=serial(energy), Cstar=serial(cstar),
                      certified_U_upper=serial(U),
                      U_threshold=rational_json(Fraction(507, 1000)),
                      elapsed_seconds=round(time.monotonic() - started, 3))
        OUTPUT.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        print(f"CERTIFIED {len(accepted)} middle intervals, U<{float(U.upper()):.9f}", flush=True)


def verify():
    saved = json.loads(OUTPUT.read_text(encoding="utf-8"))
    if not saved["certified"] or saved["precision_bits"] != BITS:
        raise AssertionError("No completed matching certificate")
    if saved["source_sha256"] != hashlib.sha256(SOURCE.read_bytes()).hexdigest():
        raise AssertionError("Source exploratory data changed")
    if saved["script_sha256"] != hashlib.sha256(Path(__file__).read_bytes()).hexdigest():
        raise AssertionError("Certificate implementation changed")
    assert parse_rational(saved["lambda_mass"]) == LAM
    assert parse_rational(saved["gamma"]) == GAMMA
    assert parse_rational(saved["epsilon"]) == EPS
    assert parse_rational(saved["T"]) == TAIL_T
    assert parse_rational(saved["target_M"]) == TARGET
    source_left, source_right, source_weights, _ = raw_measure()
    arcs = [(parse_rational(item["left"]), parse_rational(item["right"]),
             parse_rational(item["weight"])) for item in saved["arcs"]]
    assert arcs == list(zip(source_left, source_right, source_weights))
    assert sum(weight for _, _, weight in arcs) == LAM
    pieces = sorted((parse_rational(item["lo"]), parse_rational(item["hi"]))
                    for item in saved["middle_intervals"])
    assert len(pieces) == saved["middle_interval_count"] and pieces[0][0] == EPS
    assert pieces[-1][1] == TAIL_T and all(x < y for x, y in pieces)
    assert all(pieces[i][1] == pieces[i + 1][0] for i in range(len(pieces) - 1))
    with ctx.workprec(BITS):
        small = small_tail(arcs)
        large, D, C = large_tail()
        assert small.upper() < a(TARGET) and large.upper() < a(TARGET)
        assert ball_upper_rational(saved["small_tail_upper"]) < TARGET
        assert ball_upper_rational(saved["large_tail_upper"]) < TARGET
        for item in saved["middle_intervals"]:
            lo, hi = parse_rational(item["lo"]), parse_rational(item["hi"])
            result = upper_middle(lo, hi, arcs)
            assert result is not None and result[0].upper() < a(TARGET)
            assert ball_upper_rational(item["upper"]) < TARGET
        energy, cstar, U = energy_and_constant(arcs)
        assert U.upper() < a(Fraction(507, 1000))
        assert ball_upper_rational(saved["certified_U_upper"]) < Fraction(507, 1000)
    print(f"VERIFIED global tails, {len(pieces)} exact-rational middle pieces, U<0.507", flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seconds", type=int, default=300)
    parser.add_argument("--verify", action="store_true")
    args = parser.parse_args()
    if args.verify:
        verify()
    else:
        certify(args.seconds)


if __name__ == "__main__":
    sys.set_int_max_str_digits(0)
    main()
