import math
log = math.log

# DECISIVE PROBE: which per-block form, summed over blocks + small-d, actually
# stays under the platform RHS?
#
# Platform RHS (with x-term coefficient) is
#   T = 0.5*(x/q)*log(x)*(log(2*U*V/q+4)+4) + 0.89*(U*V + 2.5*q)*(8+log q)*log(2x)
#
# Candidate per-block budgets B1, B2 sum to a total we compare with T.
#
# B_tao   : X_j + 2C + (2/pi) C q log 4q        (X_j = 0.5 (x/L_j) log x)
# B_half  : 2*(X_j/2) + (2/pi) C q log 4q       = X_j + (2/pi)Cqlog4q
# B_full  : 4X_j + 2(2/pi) C q log 4q           (Cor3.5 verbatim, count 2)

def blocks_data(x, q, UV):
    out = []
    j = 0
    while 2 * j * q + q / 2 < UV:
        L = 2 * j * q + q / 2
        R = 2 * (j + 1) * q + q / 2
        out.append((L, R))
        j += 1
    return out

def envelope_sum_block(x, q, al, L, R, UV):
    C = 4 * log(2) * log(2 * x)
    Xj = 0.5 * (x / L) * log(x)
    s = 0.0
    for d in range(math.floor(L) + 1, min(math.floor(R), UV) + 1):
        if d % 2 == 0:
            continue
        sn = abs(math.sin(math.pi * 2 * al * d))
        b = C / sn if sn else float('inf')
        a = 0.5 * (x / d) * log(x) + C
        s += min(a, b)
    return s

def platform_rhs(x, q, U, V):
    UV = U * V
    return (0.5 * (x / q) * log(x) * (log(2 * UV / q + 4) + 4)
            + 0.89 * (UV + 2.5 * q) * (8 + log(q)) * log(2 * x))

# compare: how big is sum_d min(Xj, C/|sin|) relative to 2 Xj (count-1 form)
print("== per-block: s_X := sum_d min(Xj, C/|sin|)  vs  2Xj  and  4Xj ==")
for q in [4, 10, 100]:
    x = 10**6
    UV = 10**5
    al = 1 / (4 * q)
    worst1 = worst2 = 0.0
    for (L, R) in blocks_data(x, q, UV):
        C = 4 * log(2) * log(2 * x)
        Xj = 0.5 * (x / L) * log(x)
        s = 0.0
        for d in range(math.floor(L) + 1, min(math.floor(R), UV) + 1):
            if d % 2 == 0:
                continue
            sn = abs(math.sin(math.pi * 2 * al * d))
            s += min(Xj, C / sn if sn else float('inf'))
        worst1 = max(worst1, s / (2 * Xj))
        worst2 = max(worst2, s / (4 * Xj))
    print(f"  q={q:4d}  max s/(2Xj)={worst1:.4f}   max s/(4Xj)={worst2:.4f}")

print()
print("== total comparison (all blocks, alpha=1/(4q)) ==")
print(f"{'q':>6} {'U':>8} {'V':>8} {'env':>14} {'platRHS':>14} {'ratio':>8} "
      f"{'sum(2Xj)':>14} {'sum(4Xj)':>14}")
for q in [4, 10, 100, 1000]:
    for (U, V) in [(40, 40), (100, 100), (1000, 100), (10**4, 10)]:
        if U * V < q:
            continue
        for xmul in [4, 40, 400]:
            x = xmul * U * V
            al = 1 / (4 * q)
            C = 4 * log(2) * log(2 * x)
            tot = 0.0
            s2 = 0.0
            s4 = 0.0
            # small-d part
            for d in range(1, min(math.floor(q / 2), U * V) + 1):
                if d % 2 == 0:
                    continue
                sn = abs(math.sin(math.pi * 2 * al * d))
                b = C / sn if sn else float('inf')
                a = 0.5 * (x / d) * log(x) + C
                tot += min(a, b)
            for (L, R) in blocks_data(x, q, U * V):
                Xj = 0.5 * (x / L) * log(x)
                s = 0.0
                for d in range(math.floor(L) + 1, min(math.floor(R), U * V) + 1):
                    if d % 2 == 0:
                        continue
                    sn = abs(math.sin(math.pi * 2 * al * d))
                    tot += min(0.5 * (x / d) * log(x) + C,
                               C / sn if sn else float('inf'))
                s2 += 2 * Xj
                s4 += 4 * Xj
            T = platform_rhs(x, q, U, V)
            print(f"{q:6d} {U:8.0f} {V:8.0f} {tot:14.4e} {T:14.4e} {tot/T:8.4f} "
                  f"{s2:14.4e} {s4:14.4e}")
