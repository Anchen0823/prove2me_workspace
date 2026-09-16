"""Where is the slack in the halved derivation?

Three variants of the per-block bookkeeping, all with the *halved* small-d
constant, against the platform RHS:

  A  exact per-block :  sum_j [(x/L_j) log x + 2C + (2/pi) C q log 4q]
  B  Tao's crude     :  sum_j (x/L_j) log x + #blocks * C*((2/pi) q log 4q + 4q)
  C  integral test   :  (x/2q) log(2UV/q+4) log x + #blocks * C*((2/pi)q log4q + 4q)

The assembly will have to use C (or B), so we need C/RHS < 1 with margin.
"""
import math

LOG2 = math.log(2.0)


def parts(x, U, V, q):
    UV = U * V
    C = 4.0 * LOG2 * math.log(2.0 * x)
    if UV / (2.0 * q) - 0.25 >= 0:
        nblocks = int(math.floor(UV / (2.0 * q) - 0.25)) + 1
    else:
        nblocks = 0
    harm = sum(x / (2.0 * j * q + q / 2.0) * math.log(x)
               for j in range(0, nblocks))
    harm_int = (x / (2.0 * q)) * math.log(2.0 * UV / q + 4.0) * math.log(x)
    small = C * (2.0 * q + (1.0 / math.pi) * q * math.log(4.0 * q))
    return C, nblocks, harm, harm_int, small


def variants(x, U, V, q):
    C, nb, harm, harm_int, small = parts(x, U, V, q)
    a = harm + nb * (2.0 * C + (2.0 / math.pi) * C * q * math.log(4.0 * q)) + small
    b = harm + nb * C * ((2.0 / math.pi) * q * math.log(4.0 * q) + 4.0 * q) + small
    c = harm_int + nb * C * ((2.0 / math.pi) * q * math.log(4.0 * q) + 4.0 * q) + small
    return a, b, c


def rhs(x, U, V, q):
    UV = U * V
    return (0.5 * (x / q) * math.log(x) * (math.log(2 * UV / q + 4) + 4)
            + 0.89 * (UV + 2.5 * q) * (8 + math.log(q)) * math.log(2 * x))


def q_grid(UV):
    qs = []
    q = 4.0
    while q <= 4 * UV:
        qs.append(q)
        q *= 1.25
    return qs


worst = [0.0, 0.0, 0.0]
args = [None, None, None]
for U in (40.0, 100.0, 400.0, 2000.0):
    for V in (40.0, 100.0, 400.0, 2000.0):
        UV = U * V
        for xmul in (1.0, 4.0, 10.0, 100.0, 1000.0):
            x = xmul * UV * 4
            for q in q_grid(UV):
                r = rhs(x, U, V, q)
                for k, v in enumerate(variants(x, U, V, q)):
                    if v / r > worst[k]:
                        worst[k] = v / r
                        args[k] = (x, U, V, q)
for k, name in enumerate("ABC"):
    a = args[k]
    print("%s  max = %.4f   at x=%.4g U=%g V=%g q=%.4g"
          % (name, worst[k], a[0], a[1], a[2], a[3]))
