import math
log = math.log

# FULL VERBATIM CHAIN, Tao (5.14) -> (5.17), in the platform's notation.
#   C = 4 log2 log2x
#   small part  (2d <= q):  4log2 log2x * sum_{d<=q/2 odd} min(2q, 1/|sin(2pi alpha d)|)
#                           <= 2 log2 log2x * ((2/pi) q log 4q + 4q)
#   block part  (2d > q):   per block j, frozen form
#                           <= (x/L_j) log x + 2C + (2/pi) C q log 4q
#   integral test:          sum_j x/L_j <= (x/(2q)) log(2UV/q + 4)
# Total claimed <= 0.5 (x/q) log x (log(2UV/q+4)+4) + 0.89 (UV + 2.5q)(8+log q) log 2x

def C_of(x):
    return 4 * log(2) * log(2 * x)

def small_part(x, q, UV, al):
    C = C_of(x)
    # Tao's own estimate: 4 log2 log2x * sum min(2q, 1/|sin|)
    s = 0.0
    for d in range(1, min(math.floor(q / 2), UV) + 1):
        if d % 2 == 0:
            continue
        sn = abs(math.sin(math.pi * 2 * al * d))
        s += min(2 * q, 1 / sn if sn else float('inf'))
    return C * s

def block_part(x, q, UV, al):
    C = C_of(x)
    tot = 0.0
    j = 0
    while 2 * j * q + q / 2 < UV:
        L = 2 * j * q + q / 2
        R = 2 * (j + 1) * q + q / 2
        Aj = 0.5 * (x / L) * log(x)
        for d in range(math.floor(L) + 1, min(math.floor(R), UV) + 1):
            if d % 2 == 0:
                continue
            sn = abs(math.sin(math.pi * 2 * al * d))
            Bd = C / sn if sn else float('inf')
            tot += min(Aj + C, Bd)
        j += 1
    return tot

def target(x, q, U, V):
    UV = U * V
    return (0.5 * (x / q) * log(x) * (log(2 * UV / q + 4) + 4)
            + 0.89 * (UV + 2.5 * q) * (8 + log(q)) * log(2 * x))

print(f"{'q':>6} {'U':>7} {'V':>7} {'xmul':>5} {'small':>11} {'T1':>11} {'s/T1':>6} "
      f"{'block':>11} {'T2':>11} {'b/T2':>6} {'ALL':>11} {'T':>11} {'r':>6}")
worst = 0.0
for q in [4, 10, 64, 100, 1000]:
    for (U, V) in [(40, 40), (100, 100), (1000, 100), (10**4, 10)]:
        if U * V < q:
            continue
        for xmul in [4, 40, 400, 4000]:
            x = xmul * U * V
            # the admissible alpha values: 4 alpha = a/q + beta, |beta| <= 1/q^2
            for (a, beta) in [(1, 0.0), (1, 1 / q**2), (3, 0.0), (2 * q - 1, 0.0)]:
                al = (a / q + beta) / 4
                s = small_part(x, q, U * V, al)
                b = block_part(x, q, U * V, al)
                T = target(x, q, U, V)
                T1 = 0.5 * (x / q) * log(x) * (log(2 * U * V / q + 4) + 4)
                T2 = 0.89 * (U * V + 2.5 * q) * (8 + log(q)) * log(2 * x)
                r = (s + b) / T
                worst = max(worst, r)
                if r > 1.0 or s / T1 > 1 or b / T2 > 1:
                    print(f"{q:6d} {U:7.0f} {V:7.0f} {xmul:5d} {s:11.3e} {T1:11.3e} "
                          f"{s/T1:6.2f} {b:11.3e} {T2:11.3e} {b/T2:6.2f} {s+b:11.3e} "
                          f"{T:11.3e} {r:6.3f}  a={a} beta={beta:.2e}  <== OVER")
print(f"\nWORST total ratio = {worst:.4f}")
