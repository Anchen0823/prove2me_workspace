"""Exploratory double-precision scan of the 18 two-layer p=3 ratios.

This script does not certify a global maximum or an arithmetic net exponent.
Only independently proved interval bounds may be used for candidate promotion.
"""

from __future__ import annotations

import cmath
from fractions import Fraction
import json
import math
from pathlib import Path


def zlogz(z: complex) -> complex:
    return 0j if z == 0 else z * cmath.log(z)


def phase(z: complex, a1: float, a2: float, e: int) -> complex:
    return (
        -14 * a2 * math.log(a2)
        - 2 * e * a1 * math.log(a1)
        + (10 + e) * (zlogz(z) - zlogz(z + 1))
        + 7 * (zlogz(z + 1 + a2) - zlogz(z - a2))
        + e * (zlogz(z + 1 + a1) - zlogz(z - a1))
    )


def objective(y: float, a1: float, a2: float, e: int) -> float:
    return phase(complex(a2, y), a1, a2, e).real - 2 * math.pi * y


def local_max(a1: float, a2: float, e: int) -> tuple[float, float]:
    # Broad mesh plus local golden-section refinement, exploratory only.
    ys = [i / 2000 for i in range(2001)] + [
        1 + i / 250 for i in range(1, 2251)
    ]
    values = [objective(y, a1, a2, e) for y in ys]
    candidates = [0, len(ys) - 1]
    candidates += [
        i for i in range(1, len(ys) - 1)
        if values[i] >= values[i - 1] and values[i] >= values[i + 1]
    ]
    best = (values[0], 0.0)
    for i in candidates:
        lo, hi = ys[max(0, i - 1)], ys[min(len(ys) - 1, i + 1)]
        for _ in range(70):
            m1 = lo + (hi - lo) * 0.3819660112501051
            m2 = lo + (hi - lo) * 0.6180339887498949
            if objective(m1, a1, a2, e) < objective(m2, a1, a2, e):
                lo = m1
            else:
                hi = m2
        y = (lo + hi) / 2
        val = objective(y, a1, a2, e)
        if val > best[0]:
            best = (val, y)
    return best


def main() -> None:
    rows = []
    for e in (1, 2, 4):
        for rho_q in (Fraction(1, 3), Fraction(2, 3)):
            for theta_q in (Fraction(1, 2), Fraction(3, 4), Fraction(1)):
                a2_q = 3 * theta_q / (14 + 2 * e * rho_q)
                a1_q = rho_q * a2_q
                assert 14 * a2_q + 2 * e * a1_q == 3 * theta_q
                assert 0 < a1_q <= a2_q < Fraction(1, 4)
                rho, theta = float(rho_q), float(theta_q)
                a2, a1 = float(a2_q), float(a1_q)
                u, y = local_max(a1, a2, e)
                rows.append({
                    "e": e, "rho": rho, "theta": theta,
                    "rho_exact": str(rho_q), "theta_exact": str(theta_q),
                    "alpha1_exact": str(a1_q), "alpha2_exact": str(a2_q),
                    "alpha1": a1, "alpha2": a2,
                    "U_exploratory": u, "y_exploratory": y,
                    "U_plus_9_trivial_arithmetic_exploratory": u + 9,
                })
    result = {
        "status": "exploratory_double_precision_only",
        "warning": "No interval certification, global-max proof, or G-asymptotic included.",
        "rows": rows,
    }
    path = Path(__file__).resolve().parents[1] / "verification" / "analytic-layer-exploratory.json"
    path.write_text(json.dumps(result, indent=2), encoding="utf-8")
    print(f"wrote {path}")
    for row in sorted(rows, key=lambda z: z["U_exploratory"]):
        print(
            f"e={row['e']} rho={row['rho']:.6g} theta={row['theta']:.6g}"
            f" U~{row['U_exploratory']:.6f} y~{row['y_exploratory']:.6f}"
            f" U+9~{row['U_plus_9_trivial_arithmetic_exploratory']:.6f}"
        )


if __name__ == "__main__":
    main()
