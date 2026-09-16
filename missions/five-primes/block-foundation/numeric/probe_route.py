import math
log = math.log

# The "2Xj per block" route fails.  Test the ACTUAL route that could work:
#
# On a block (L, R], L = 2jq + q/2, R = L + 2q, every odd d in it satisfies
#   (x/d) log x  <=  (x/L) log x      (since d >= L+1 > L)
# and                  >=  (x/R) log x
# so sum_{d odd in block} (1/2)(x/d) log x  <=  q_term * (1/2)(x/L) log x
# where q_term = #{odd d in block} <= q/2 + 1.
#
# And the C-terms:  sum_d C = (#d) * C.
#
# And the B-alternative: if B_d >= frozen A on part of the block, min picks A.
# Key fact to test:  on the block, min(A_d, B_d) <= A_L + C  ALWAYS
# (i.e. we may always use the *frozen* first alternative A_L + C, because
#  either B_d is small and then min = B_d <= ? no...)
#
# Correct elementary bound (no Cor 3.5 at all):
#   min(A_d, B_d) <= A_d  <=  (1/2)(x/L) log x + C   for all d in block.
# That is TRIVIAL and gives  #d * ((1/2)(x/L)log x + C) ~ (q/2)X_j : far too big.
#
# So the B-side MUST be used.  Test: how much does B actually save?

def cost(x, q, UV, al, use_min=True):
    C = 4 * log(2) * log(2 * x)
    tot = 0.0
    L0 = q / 2
    # small d
    for d in range(1, min(math.floor(L0), UV) + 1):
        if d % 2 == 0:
            continue
        sn = abs(math.sin(math.pi * 2 * al * d))
        b = C / sn if sn else float('inf')
        a = 0.5 * (x / d) * log(x) + C
        tot += min(a, b) if use_min else a
    # blocks
    for j in range(0, int(UV / (2 * q)) + 1):
        L = 2 * j * q + q / 2
        R = 2 * (j + 1) * q + q / 2
        for d in range(math.floor(L) + 1, min(math.floor(R), UV) + 1):
            if d % 2 == 0:
                continue
            sn = abs(math.sin(math.pi * 2 * al * d))
            b = C / sn if sn else float('inf')
            a = 0.5 * (x / d) * log(x) + C
            tot += min(a, b) if use_min else a
    return tot

def plat(x, q, U, V):
    UV = U * V
    return (0.5 * (x / q) * log(x) * (log(2 * UV / q + 4) + 4)
            + 0.89 * (UV + 2.5 * q) * (8 + log(q)) * log(2 * x))

print("== how much does the B-alternative actually save? ==")
for q in [4, 100]:
    for (U, V) in [(40, 40), (100, 100)]:
        for xmul in [4, 400]:
            x = xmul * U * V
            al = 1 / (4 * q)
            t_min = cost(x, q, U * V, al, True)
            t_a = cost(x, q, U * V, al, False)
            T = plat(x, q, U, V)
            print(f"  q={q:4d} U=V={U:4d} x={x:10.0f}: min={t_min:.4e} "
                  f"noMin={t_a:.4e} ratio_min={t_min/T:.4f} ratio_noMin={t_a/T:.4f}")

print()
print("== is sum_d min(A_d,B_d) <= (x/(2q))log(2UV/q+4)*log x + K*(q-ish)? ==")
# Test the SHAPE of the target: first term is (x/(2q)) log x log(2UV/q+4).
# The sum of A_d (even without B) over ALL d is ~ (x/2)log x * H ~ (x/2) log x * log(UV/q).
# Note log(2UV/q+4) ~ log(2UV/q), and H_{UV, step 2q} ~ (1/(2q)) log(UV/q).
# So (x/(2q)) log x log(UV/q) matches sum A_d / ? -> check factor.
print()
print("== factor check: sum_d (1/2)(x/d)log x  vs  (x/(2q)) log x log(2UV/q+4) ==")
for q in [4, 100, 1000]:
    for UV in [1600, 10**4, 10**5]:
        x = 4 * UV
        s = sum(0.5 * (x / d) * log(x) for d in range(1, UV + 1) if d % 2 == 1)
        rhs = 0.5 * (x / q) * log(x) * (log(2 * UV / q + 4) + 4)
        print(f"  q={q:5d} UV={UV:8d}: sumA={s:.4e} rhs1={rhs:.4e} s/rhs1={s/rhs:.4f}")
