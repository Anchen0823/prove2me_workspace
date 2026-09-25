"""Real exponents for the rational-shift D=6,8 ζ(9) construction.

Only the strict-interior entries use a finite maximizing saddle.  The
endpoint supremum is at infinity; m=0 is a separate polynomial regime.
All printed decimals are exploratory, not interval certificates.
"""

from __future__ import annotations

import math
from fractions import Fraction


def phase(D: int, a: float, x: float) -> float:
    assert D in (6, 8) and x > a > 0
    return (
        -2 * D * a * math.log(a)
        + 10 * x * math.log(x)
        + D * (x + 1 + a) * math.log(x + 1 + a)
        - D * (x - a) * math.log(x - a)
        - 10 * (x + 1) * math.log(x + 1)
    )


def derivative(D: int, a: float, x: float) -> float:
    assert x > a
    return 10 * math.log(x / (x + 1)) + D * math.log((x + 1 + a) / (x - a))


def peak(D: int, a: float) -> tuple[float, float]:
    endpoint = (10 - D) / (2 * D)
    assert 0 < a < endpoint
    lo = math.nextafter(a, math.inf)
    hi = max(1.0, 2 * a)
    while derivative(D, a, hi) > 0:
        hi *= 2
    for _ in range(100):
        mid = (lo + hi) / 2
        if derivative(D, a, mid) > 0:
            lo = mid
        else:
            hi = mid
    x = (lo + hi) / 2
    return x, phase(D, a, x)


def edge(D: int, a: float) -> float:
    if a == 0:
        return 0.0
    return (
        (10 - 2 * D) * a * math.log(a)
        + D * (1 + 2 * a) * math.log(1 + 2 * a)
        - 10 * (1 + a) * math.log(1 + a)
    )


def log_r_exact(D: int, n: int, m: int, t: float) -> float:
    assert t > m
    M = D * (n + 2 * m) + 1
    return (
        (10 - D) * math.lgamma(n + 1)
        - 2 * D * math.lgamma(m + 1)
        - M * math.log(D)
        + math.lgamma(D * (t + n + m) + 1)
        - math.lgamma(D * (t - m))
        - 10 * (math.lgamma(t + n + 1) - math.lgamma(t))
    )


def log_asymptotic(D: int, n: int, m: int, x: float) -> float:
    a = m / n
    power = -(3 * D + 8) / 2
    log_amp = (
        (10 - 3 * D) / 2 * math.log(2 * math.pi)
        - D * math.log(a)
        + 0.5 * math.log((x - a) * (x + 1 + a))
        - 5 * math.log(x * (x + 1))
    )
    return n * phase(D, a, x) + power * math.log(n) + log_amp


def main() -> None:
    for D, fractions in (
        (6, [Fraction(0), Fraction(1, 12), Fraction(1, 6), Fraction(1, 4), Fraction(1, 3)]),
        (8, [Fraction(0), Fraction(1, 24), Fraction(1, 12), Fraction(1, 8)]),
    ):
        endpoint = Fraction(10 - D, 2 * D)
        for frac in fractions:
            a = float(frac)
            if frac == 0:
                print(f"D={D} a=0 edge=0, polynomial regime")
            elif frac == endpoint:
                print(f"D={D} a={frac} peak=infinity rate={-2 * D * a * math.log(a):.12f}")
            else:
                x, rate = peak(D, a)
                print(f"D={D} a={frac} peak={x:.12f} rate={rate:.12f} edge={edge(D,a):.12f}")


if __name__ == "__main__":
    main()
