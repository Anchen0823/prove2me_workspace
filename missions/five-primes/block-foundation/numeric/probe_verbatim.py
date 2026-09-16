import math
log = math.log

# Tao 5.2, verbatim per-block step, checked in the CORRECT variables.
#
# Frozen first alternative on the block (L_j, R_j], L_j = 2jq + q/2:
#     F_j := (1/2)(x/L_j) log x + C        [C = 4 log2 log2x]
# The block's envelope-restricted min-sum is
#     S_j := sum_{odd d in block} min( (1/2)(x/d)log x + C , C/|sin(2 pi alpha d)| )
#
# TAO'S CLAIM (his display, verbatim):
#     S_j <= x/L_j * log x + 2C + (2/pi) C q log 4q
# with the RHS = "Cor 3.5 applied with A := (1/2)(x/L_j) log x" which returns
#     2*A + (2/pi)*C*q*log4q = x/L_j * log x + (2/pi) C q log 4q
# plus the 2C from the frozen C.  Check BOTH the coefficient-1 form and 2x.

def C_of(x):
    return 4 * log(2) * log(2 * x)

def S_j(x, q, j, al, UV):
    L = 2 * j * q + q / 2
    R = 2 * (j + 1) * q + q / 2
    C = C_of(x)
    s = 0.0
    cnt = 0
    for d in range(math.floor(L) + 1, min(math.floor(R), UV) + 1):
        if d % 2 == 0:
            continue
        cnt += 1
        sn = abs(math.sin(math.pi * 2 * al * d))
        Bd = C / sn if sn else float('inf')
        Ad = 0.5 * (x / d) * log(x) + C
        s += min(Ad, Bd)
    return s, cnt

def frozen_min(x, q, j, al, UV):
    """sum_d min( (1/2)(x/L_j)log x + C , C/|sin| )  -- the FROZEN form."""
    L = 2 * j * q + q / 2
    R = 2 * (j + 1) * q + q / 2
    C = C_of(x)
    Aj = 0.5 * (x / L) * log(x)
    s = 0.0
    for d in range(math.floor(L) + 1, min(math.floor(R), UV) + 1):
        if d % 2 == 0:
            continue
        sn = abs(math.sin(math.pi * 2 * al * d))
        Bd = C / sn if sn else float('inf')
        s += min(Aj + C, Bd)
    return s

print("=== (a) does freezing INSIDE the min lose anything?  S_j <= frozen_min_j ? ===")
for q in [4, 10, 100]:
    x = 10**6; UV = 10**5; al = 1 / (4 * q)
    w = 0.0; bad = 0
    for j in range(0, int(UV / (2 * q)) + 1):
        s, _ = S_j(x, q, j, al, UV)
        f = frozen_min(x, q, j, al, UV)
        if s > f * (1 + 1e-12):
            bad += 1
        w = max(w, s / f if f else 0)
    print(f"  q={q:4d}: #blocks where frozen is smaller = {bad},  max S/frozen = {w:.6f}")

print()
print("=== (b) Tao's display: frozen_min_j <= (x/L_j) log x + 2C + (2/pi)Cq log4q ? ===")
for q in [4, 10, 100]:
    for al in [1 / (4 * q), 1 / (2 * q), 0.3121]:
        x = 10**6; UV = 10**5
        bad = 0; mx = 0.0
        for j in range(0, int(UV / (2 * q)) + 1):
            f = frozen_min(x, q, j, al, UV)
            L = 2 * j * q + q / 2
            C = C_of(x)
            rhs = (x / L) * log(x) + 2 * C + (2 / math.pi) * C * q * log(4 * q)
            if f > rhs:
                bad += 1
            mx = max(mx, f / rhs if rhs else 0)
        print(f"  q={q:4d} al={al:.6f}: #violating = {bad}  max f/rhs = {mx:.4f}")

print()
print("=== (c) the stronger form with 2X_j = (x/L_j) log x: same thing. "
      "So Tao's RHS == (x/L_j)log x + 2C + (2/pi)Cq log4q. ===")
print("=== (d) but does the platform need the *weaker* X_j or the *stronger* 2X_j? ===")
print("    (sum over blocks of (x/L_j)log x) vs first term (x/(2q))log x (log(2UV/q+4)+4)")
for q in [4, 10, 100]:
    for UV in [1600, 10**4, 10**5]:
        x = 4 * UV
        s = 0.0
        j = 0
        while 2 * j * q + q / 2 < UV:
            L = 2 * j * q + q / 2
            s += (x / L) * log(x)
            j += 1
        T1 = 0.5 * (x / q) * log(x) * (log(2 * UV / q + 4) + 4)
        print(f"  q={q:5d} UV={UV:8d}: sum(x/L)={s:.4e} T1={T1:.4e} ratio={s/T1:.4f}")
