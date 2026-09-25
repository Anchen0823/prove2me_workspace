"""Independent numeric audit of the zeta9 analytic constants.

Checks, against the archived certificates in
missions/zeta9/verification/analytic-vertical-bound.json and summary.json:

 (1) Gamma(alpha) = 7 * int_1^inf 1_{{x}+2{alpha x}>=2} / x^2 dx
     computed by exact rational cell decomposition + Taylor tail;
 (2) 0 <= Gamma(alpha) <= 14 alpha;
 (3) sup_{y>=0} H_alpha(y) computed from the closed form, vs archived bounds;
 (4) H'_alpha(y) = 3pi/2 - 10 atan(y/alpha) - 7 atan(y/(1+2a)) + 10 atan(y/(1+a))
     checked against a numerical derivative of the closed form (C6);
 (5) H''(y)*(alpha^2+y^2)*((1+2a)^2+y^2)*((1+a)^2+y^2) vs the archived
     hsecond_numerator quadratic in x = y^2;
 (6) the archived combined upper bounds (summary.json) vs
     (9-Gamma) + sup H.
"""
import sys, os, json
sys.path.insert(0, os.path.join("tmp", "zeta7", "exact_packages"))
from fractions import Fraction as Fr
from mpmath import mp, mpf, pi, log, sqrt, atan, zeta, polygamma, findroot

mp.dps = 40
ALPHAS = [Fr(1, 28), Fr(1, 14), Fr(3, 28), Fr(1, 7), Fr(5, 28), Fr(3, 14)]
ARCH_GAMMA = {
    "1/28": (0.14171563, 0.14171565),
    "1/14": (0.28254068, 0.28254070),
    "3/28": (0.42662800, 0.42662801),
    "1/7": (0.57820646, 0.57820651),
    "5/28": (0.70905586, 0.70905588),
    "3/14": (0.85210820, 0.85210822),
}
ARCH_SUPH = {
    "1/28": 0.671769718688, "1/14": 1.167676972547, "3/28": 1.609438937754,
    "1/7": 2.021873399673, "5/28": 2.416195251742, "3/14": 2.798637880122,
}
ARCH_HSEC = {
    "1/28": [Fr(-534615, 1229312), Fr(2395, 784), Fr(5, 2)],
    "1/14": [Fr(-5025, 4802), Fr(43, 14), Fr(2)],
    "3/28": [Fr(-2297193, 1229312), Fr(2385, 784), Fr(3, 2)],
    "1/7": [Fr(-144, 49), Fr(145, 49), Fr(1)],
    "5/28": [Fr(-5282475, 1229312), Fr(2207, 784), Fr(1, 2)],
    "3/14": [Fr(-115005, 19208), Fr(255, 98), Fr(0)],
}
ARCH_COMBINED = {
    "1/28": "3904463159046312514133370805231485981/409700000000000000000000000000000000",
    "1/14": "2024970169433289294258970847819448239/204850000000000000000000000000000000",
    "3/28": "2085948820184210505299859953757828193/204850000000000000000000000000000000",
    "1/7": "1684765821837469597524901818377163089/161319375000000000000000000000000000",
    "5/28": "1370848439084839762535069460136261/128031250000000000000000000000000",
    "3/14": "2242396604822997989242763319234545523/204850000000000000000000000000000000",
}


def support_cells(alpha):
    """Exact decomposition of {u in [0,b) : {u}+2{alpha u} >= 2} into intervals."""
    a, b = alpha.numerator, alpha.denominator
    cuts = {Fr(0), Fr(b)}
    cuts |= {Fr(i) for i in range(b + 1)}
    cuts |= {Fr(m * b, a) for m in range(a + 1)}
    cuts = sorted(cuts)
    out = []
    for lo, hi in zip(cuts, cuts[1:]):
        if hi <= lo:
            continue
        mid = (lo + hi) / 2
        p = mid.numerator // mid.denominator
        k = (alpha * mid).numerator // (alpha * mid).denominator
        thr = Fr(p + 2 * k + 2, 1) / (1 + 2 * alpha)
        l, r = max(lo, thr), hi
        if r > l:
            out.append((l, r))
    return out, b


def gamma_numeric(alpha, periods=200, taylor_terms=6):
    cells, b = support_cells(alpha)
    Afact = {}
    for i in range(taylor_terms):
        Afact[i] = sum((r ** (i + 1) - l ** (i + 1)) / Fr(i + 1) for l, r in cells)
    total = mpf(0)
    for n in range(periods):                      # exact per period
        for l, r in cells:
            total += 1 / (n * b + mpf(l)) - 1 / (n * b + mpf(r))
    tail = mpf(0)
    for i in range(taylor_terms):                 # Taylor in u/(nb)
        s = zeta(i + 2) - sum(mpf(1) / mpf(n) ** (i + 2) for n in range(1, periods))
        tail += (i + 1) * (-1) ** i * mpf(Afact[i]) * s / mpf(b) ** (i + 2)
    return 7 * (total + tail), Afact[0], b


def Phi(w, alpha):
    a = mpf(alpha)
    lw = log(w); l1 = log(w + 1 + a); l2 = log(w - a); l3 = log(w + 1)
    return (-14 * a * log(a) + 10 * w * lw + 7 * (w + 1 + a) * l1
            - 7 * (w - a) * l2 - 10 * (w + 1) * l3)


def H(y, alpha):
    a = mpf(alpha); w = a + 1j * y
    return Phi(w, alpha).real - 2 * pi * y


def Hprime(y, alpha):
    a = mpf(alpha)
    return 3 * pi / 2 - 10 * atan(y / a) - 7 * atan(y / (1 + 2 * a)) + 10 * atan(y / (1 + a))


def sup_H(alpha):
    a = mpf(alpha)
    best, by = -mpf(10) ** 3, mpf(0)
    for i in range(0, 2001):
        y = i * mpf(1) / 40
        v = H(y, a)
        if v > best:
            best, by = v, y
    y = findroot(lambda t: Hprime(t, a), by if by else mpf(1) / 100)
    return H(y, a), y


print("=== (1)(2) Gamma(alpha) ===")
for al in ALPHAS:
    g, A0, b = gamma_numeric(al)
    lo, hi = ARCH_GAMMA[str(al)]
    ok = lo <= float(g) <= hi
    print(f"alpha={str(al):>6}  Gamma={mp.nstr(g, 12):>14}  archive=[{lo},{hi}]  "
          f"inside={ok}  14alpha={float(14*al):.6f}  G<=14a={float(g)<=float(14*al)}  b={b}")

print()
print("=== (3) sup H ===")
for al in ALPHAS:
    v, y = sup_H(al)
    arch = ARCH_SUPH[str(al)]
    print(f"alpha={str(al):>6}  supH={mp.nstr(v, 12):>14} at y={mp.nstr(y, 8):>10}  "
          f"archive_upper={arch}  H<=arch={float(v) <= arch}  H(0)={mp.nstr(H(0, al), 10)}")

print()
print("=== (4) H' formula vs numerical derivative of the closed form ===")
for al in ALPHAS:
    for y in [mpf(1)/1000, mpf(1)/10, mpf(1), mpf(5), mpf(40)]:
        num = mp.diff(lambda t: H(t, al), y, 1)
        print(f"alpha={str(al):>6} y={mp.nstr(y,6):>8} H'formula={mp.nstr(Hprime(y, al), 12):>16} "
              f"numeric={mp.nstr(num, 12):>16} diff={mp.nstr(abs(num - Hprime(y, al)), 4)}")
    break  # one alpha is enough for the identity: it is symbolic in alpha
print()
print("=== (5) H'' polynomial vs archived hsecond_numerator ===")
for al in ALPHAS:
    a = mpf(al); c0, c1, cx = ARCH_HSEC[str(al)]
    for y in [mpf(3)/10, mpf(1), mpf(3), mpf(20)]:
        val = mp.diff(lambda t: H(t, al), y, 2) * (a**2 + y**2) * ((1 + 2*a) ** 2 + y**2) * ((1 + a) ** 2 + y**2)
        poly = mpf(c0) + mpf(c1) * y**2 + mpf(cx) * y**4
        print(f"alpha={str(al):>6} y={mp.nstr(y,6):>8} lhs={mp.nstr(val, 14):>20} poly={mp.nstr(poly, 14):>20} "
              f"relerr={mp.nstr(abs(val-poly)/abs(poly), 3)}")
    print(f"        leading coeff archived={cx}  3-14alpha={3 - 14*al}  match={cx == 3 - 14*al}")

print()
print("=== (6) combined bounds ===")
for al in ALPHAS:
    a = mpf(al)
    g, _, _ = gamma_numeric(al)
    v, _ = sup_H(al)
    comb = 9 - g + v
    q = mpf(ARCH_COMBINED[str(al)].split("/")[0]) / mpf(ARCH_COMBINED[str(al)].split("/")[1])
    ceil6 = mp.ceil(comb * 10**6) / 10**6
    print(f"alpha={str(al):>6} 9-Gamma={mp.nstr(9-g,10):>12} supH={mp.nstr(v,10):>12} "
          f"sum={mp.nstr(comb,12):>15} ceil6={mp.nstr(ceil6,10):>10} archived={mp.nstr(q,12):>15} "
          f"archived_is_larger={float(q) >= float(comb)}")
