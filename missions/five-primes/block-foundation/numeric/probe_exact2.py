"""Exact evaluation of Tao's derivation, with the j=0 term restored.

Correct integral test (f decreasing, f(j) = x/(2jq + q/2)):

    sum_{j=0}^{J} f(j) <= f(0) + int_0^J f
                        = 2x/q + (x/2q) log(4J+1)
                        <= 2x/q + (x/2q) log(2UV/q)          [4J+1 <= 2UV/q]
                        <= 2x/q + (x/2q) log(2UV/q + 4).

The platform's first term is exactly `log x * (2x/q + (x/2q) log(2UV/q+4))`
= `0.5 (x/q) log x (log(2UV/q+4) + 4)`.  So the whole of the first term is
consumed by the harmonic part and Term 2 must carry the cosecant part alone:

    #blocks * C * ((2/pi) q log 4q + 4q)  +  C * (2q + (1/pi) q log 4q)
        <=  0.89 (UV + 2.5 q)(8 + log q) log(2x)                        (*)

with #blocks = floor(UV/(2q) - 1/4) + 1 (zero when UV/(2q) < 1/4).
"""
import math

LOG2 = math.log(2.0)


def cosec_part(x, q, halved):
    C = 4.0 * LOG2 * math.log(2.0 * x)
    if halved:
        return C * (2.0 * q + (1.0 / math.pi) * q * math.log(4.0 * q))
    return C * (4.0 * q + (2.0 / math.pi) * q * math.log(4.0 * q))


def term2_lhs(x, U, V, q, halved):
    UV = U * V
    C = 4.0 * LOG2 * math.log(2.0 * x)
    if UV / (2.0 * q) - 0.25 >= 0:
        nb = int(math.floor(UV / (2.0 * q) - 0.25)) + 1
    else:
        nb = 0
    return nb * C * ((2.0 / math.pi) * q * math.log(4.0 * q) + 4.0 * q) \
        + cosec_part(x, q, halved)


def term2_rhs(x, U, V, q):
    UV = U * V
    return 0.89 * (UV + 2.5 * q) * (8 + math.log(q)) * math.log(2.0 * x)


def q_grid(UV):
    qs, q = [], 4.0
    while q <= 8 * UV + 64:
        qs.append(q)
        q *= 1.2
    return qs


for halved in (True, False):
    worst, arg = 0.0, None
    for U in (40.0, 100.0, 400.0, 2000.0, 10000.0):
        for V in (40.0, 100.0, 400.0, 2000.0, 10000.0):
            UV = U * V
            for xmul in (1.0, 4.0, 10.0, 100.0, 1000.0):
                x = xmul * UV * 4
                for q in q_grid(UV):
                    r = term2_lhs(x, U, V, q, halved) / term2_rhs(x, U, V, q)
                    if r > worst:
                        worst, arg = r, (x, U, V, q)
    print("halved=%-5s  max(Term2 LHS / Term2 RHS) = %.4f  at x=%.4g U=%g V=%g q=%.4g"
          % (halved, worst, arg[0], arg[1], arg[2], arg[3]))
