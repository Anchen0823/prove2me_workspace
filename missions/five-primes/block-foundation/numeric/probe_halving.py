"""Decide whether the *halved* small-d constant is needed.

Tao's derivation of (5.17), evaluated exactly, against the platform RHS of
`TaoFivePrimes.theorem51_typeI_block_summation`.

  per block j :  (x/L_j) log x + 2C + (2/pi) C q log 4q
                 <= (x/L_j) log x + C*((2/pi) q log 4q + 4q)      (q >= 1/2)
  small d     :  C * sum_{odd d <= q/2} min(2q, 1/|sin(2 pi d a)|)
                 <= C * (2q + (1/pi) q log 4q)        [halved by symmetry]
              or  C * (4q + (2/pi) q log 4q)        [Cor 3.5 as published]
  blocks      :  sum_j x/L_j <= (x/2q) log(2UV/q + 4)

RHS (platform) = 0.5 (x/q) log x (log(2UV/q+4) + 4)
                 + 0.89 (UV + 2.5 q)(8 + log q) log(2x)
"""
import math

LOG2 = math.log(2.0)


def derivation(x, U, V, q, halved):
    UV = U * V
    C = 4.0 * LOG2 * math.log(2.0 * x)
    # blocks j = 0..J with j <= UV/(2q) - 1/4
    nblocks = 0
    if UV / (2.0 * q) - 0.25 >= 0:
        nblocks = int(math.floor(UV / (2.0 * q) - 0.25)) + 1
    # harmonic part
    if nblocks > 0:
        harm = sum(x / (2.0 * j * q + q / 2.0) * math.log(x)
                   for j in range(0, nblocks))
    else:
        harm = 0.0
    per_block_cosec = C * ((2.0 / math.pi) * q * math.log(4.0 * q) + 4.0 * q)
    if halved:
        small = C * (2.0 * q + (1.0 / math.pi) * q * math.log(4.0 * q))
    else:
        small = C * (4.0 * q + (2.0 / math.pi) * q * math.log(4.0 * q))
    return harm + nblocks * per_block_cosec + small


def rhs(x, U, V, q):
    UV = U * V
    return (0.5 * (x / q) * math.log(x) * (math.log(2 * UV / q + 4) + 4)
            + 0.89 * (UV + 2.5 * q) * (8 + math.log(q)) * math.log(2 * x))


def sweep(halved):
    worst = 0.0
    arg = None
    for U in (40.0, 100.0, 400.0):
        for V in (40.0, 100.0, 400.0):
            UV = U * V
            for xmul in (1.0, 4.0, 10.0, 100.0, 1000.0):
                x = xmul * UV * 4  # UV <= x/4
                qq = 4
                while qq <= max(4.0, 4 * UV):
                    r = derivation(x, U, V, qq, halved) / rhs(x, U, V, qq)
                    if r > worst:
                        worst, arg = r, (x, U, V, qq)
                    qq *= 2.0 if qq < 64 else 1.6
                    if qq > 1e7:
                        break
    return worst, arg


for halved in (True, False):
    w, a = sweep(halved)
    print("halved=%-5s  max(derivation/RHS) = %.4f   at x=%.3g U=%g V=%g q=%g"
          % (halved, w, a[0], a[1], a[2], a[3]))
