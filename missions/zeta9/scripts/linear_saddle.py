"""Explore and certify the *upper* contour exponent for the short-zero ζ(9) form.

This does not prove a saddle asymptotic, nonvanishing, or irrationality.  The
certificate only bounds sup_y H_alpha(y) for the six prescribed alpha values.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
import math
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / "missions/zeta9/verification/analytic-vertical-bound.json"
ALPHAS = [Fraction(k, 28) for k in range(1, 7)]
BITS = 256


def hprime_float(a: float, y: float) -> float:
    return (1.5 * math.pi - 10 * math.atan(y / a)
            - 7 * math.atan(y / (1 + 2 * a))
            + 10 * math.atan(y / (1 + a)))


def h_float(a: float, y: float) -> float:
    return (-14 * a * math.log(a)
            + 5 * a * math.log(a*a + y*y)
            + 3.5 * (1 + 2*a) * math.log((1 + 2*a)**2 + y*y)
            - 5 * (1 + a) * math.log((1 + a)**2 + y*y)
            + y * hprime_float(a, y))


def poly_mul(p: list[Fraction], q: list[Fraction]) -> list[Fraction]:
    out = [Fraction(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            out[i+j] += x*y
    return out


def hsecond_numerator(a: Fraction) -> list[Fraction]:
    """Numerator of H'' over three strictly positive quadratic factors.

    Variable x is y^2.  A negative constant, positive linear coefficient and
    nonnegative quadratic coefficient prove that H'' changes sign exactly once.
    """
    factors = [[a*a, Fraction(1)], [(1+2*a)**2, Fraction(1)],
               [(1+a)**2, Fraction(1)]]
    terms = [(-10*a, poly_mul(factors[1], factors[2])),
             (-7*(1+2*a), poly_mul(factors[0], factors[2])),
             (10*(1+a), poly_mul(factors[0], factors[1]))]
    return [sum(c*p[k] for c, p in terms) for k in range(3)]


def exploratory() -> None:
    for alpha in ALPHAS:
        a = float(alpha)
        lo, hi = 0.0, 1.0
        assert hprime_float(a, lo) > 0 and hprime_float(a, hi) < 0
        for _ in range(80):
            mid = (lo + hi) / 2
            if hprime_float(a, mid) > 0:
                lo = mid
            else:
                hi = mid
        y = (lo + hi) / 2
        print(f"alpha={alpha!s:>5} y_vertical={y:.12g} "
              f"H_vertical={h_float(a,y):.12g} "
              f"H_at_edge={h_float(a,0):.12g}")


def certify() -> None:
    sys.path.insert(0, str(ROOT / "tmp/zeta7/exact_packages"))
    from flint import arb, ctx, fmpq

    def aq(value: Fraction):
        return arb(fmpq(value.numerator, value.denominator))

    def hprime(a: Fraction, y):
        aa = aq(a)
        return (arb.pi() * fmpq(3, 2) - 10*(y/aa).atan()
                - 7*(y/(1+2*aa)).atan()
                + 10*(y/(1+aa)).atan())

    def h(a: Fraction, y):
        aa = aq(a)
        return (-14*aa*aa.log() + 5*aa*(aa*aa+y*y).log()
                + fmpq(7, 2)*(1+2*aa)*((1+2*aa)**2+y*y).log()
                - 5*(1+aa)*((1+aa)**2+y*y).log()
                + y*hprime(a, y))

    def upper_decimal(ball, digits: int = 12) -> str:
        mid, rad, exponent = ball.mid_rad_10exp(60)
        exponent = int(exponent)
        upper = Fraction(int(mid)+int(rad), 1)
        upper *= 10**exponent if exponent >= 0 else Fraction(1, 10**(-exponent))
        scale = 10**digits
        ceil_scaled = -(-upper.numerator * scale // upper.denominator)
        rounded = Fraction(ceil_scaled, scale)
        assert ball.upper() < aq(rounded)
        return f"{ceil_scaled//scale}.{ceil_scaled%scale:0{digits}d}"

    rows = []
    with ctx.workprec(BITS):
        for alpha in ALPHAS:
            c = hsecond_numerator(alpha)
            assert c[0] < 0 and c[1] > 0 and c[2] >= 0
            # Therefore H' decreases, then increases toward -2π; it has one
            # positive root.  These dyadic signs isolate the global maximizer.
            lo, hi = Fraction(0), Fraction(1)
            assert hprime(alpha, aq(lo)).lower() > 0
            assert hprime(alpha, aq(hi)).upper() < 0
            for _ in range(45):
                mid = (lo+hi)/2
                val = hprime(alpha, aq(mid))
                if val.lower() > 0:
                    lo = mid
                elif val.upper() < 0:
                    hi = mid
                else:
                    raise ArithmeticError("Increase Arb precision to isolate root")
            yball = aq(lo).union(aq(hi))
            hball = h(alpha, yball)
            upper = upper_decimal(hball)
            assert hball.upper() < arb(upper)
            rows.append({"alpha": str(alpha), "root_lo": str(lo),
                         "root_hi": str(hi),
                         "hsecond_numerator": [str(v) for v in c],
                         "H_global_strict_upper": upper})
            print(f"alpha={alpha} H_global<{upper} root∈({lo},{hi})")
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps({"scope": "vertical-contour real-part upper bound; no nonvanishing",
                               "precision_bits": BITS, "rows": rows}, indent=2)+"\n",
                   encoding="utf-8")


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--certify", action="store_true")
    args = p.parse_args()
    certify() if args.certify else exploratory()
