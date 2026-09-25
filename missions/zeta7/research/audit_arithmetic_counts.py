"""Independent finite-class audit of scripts/arithmetic_bounds.py.

This checks limiting integrands against finite residue-class/Legendre counts.
It is numerical evidence about the implementation, not a proof of a prime sum.
"""

import json
import sys
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
import arithmetic_bounds as formulas


def ell(bound, a, p):
    return max(0, (bound - a) // p + 1) + max(0, (bound - (p - a)) // p + 1)


def scalar_valuation(k, n, h, p, q):
    # p^2 > 2h in every case used here, so higher Legendre powers vanish.
    return (
        2 * h * (k // p)
        - 4 * q * h * (n // p)
        - 2 * sum((2 * i) // p for i in range(1, h))
    )


def finite_inner(p, x, alpha, q=4, s=7):
    k = round(x * p)
    n = round(alpha * k)
    h = k - n
    m = (p - 1) // 2
    classes = [(ell(k, a, p), q * ell(n, a, p), a) for a in range(1, m + 1)]
    # Zero-square block is fixed-dimensional and vanishes after division by p.
    t, extra = divmod(h + q * (n - n // p), m)
    allocated = {a for _, _, a in sorted(classes, key=lambda item: -item[0])[:extra]}
    gamma = 0
    for pole_count, b, a in classes:
        dimension = t - b + int(a in allocated)
        if dimension < 0:
            raise AssertionError("negative inner class dimension")
        gamma += dimension * (dimension + 2 * b - pole_count - s)
    direct = -(gamma + scalar_valuation(k, n, h, p, q)) / p
    limit = formulas.inner_R(k / p, n / k, q, s)
    return {"p": p, "x": k / p, "direct": direct, "limit": limit, "error": direct - limit}


def finite_outer(p, y, alpha, q=4, s=7):
    k = round(p / y)
    n = round(alpha * k)
    h = k - n
    if not 2 * n < p:
        raise AssertionError("the one-removed-pole hypothesis fails")
    m = (p - 1) // 2
    cost = zero_weights = 0
    if k >= p:
        for a in range(1, m + 1):
            pole_count = ell(k, a, p)
            removed = int(a <= n)
            for i in range(pole_count - removed):
                weight = min(0, i + q * removed - (pole_count + s - 1) / 2) if i < pole_count - 2 else 0
                cost -= 2 * weight
                zero_weights += weight == 0
    else:
        zero_weights = h
    rank = max(0, k + (2 * q - 2) * n - 3 * p + 3)
    direct = (cost + min(zero_weights, rank) - scalar_valuation(k, n, h, p, q)) / k
    residue, zeros, limiting_rank, scalar = formulas.outer_components(p / k, n / k, q, s)
    limit = residue + min(zeros, limiting_rank) + scalar
    return {"p": p, "y": p / k, "direct": direct, "limit": limit, "error": direct - limit}


if __name__ == "__main__":
    results = []
    for prime in (1009, 10007, 100003):
        for x_value in (3.17, 5.73, 11.21):
            results.append({"range": "inner", **finite_inner(prime, x_value, .075)})
        for y_value in (.37, .43, .51, .67, .91, 1.13, 1.57):
            results.append({"range": "outer", **finite_outer(prime, y_value, .075)})
    print(json.dumps(results, indent=2))
