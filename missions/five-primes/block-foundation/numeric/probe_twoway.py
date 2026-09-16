import math
log = math.log

# DECISIVE: check Tao's OWN two-way split against the platform's two terms.
#   small-d part  (2d <= q)   <- should be <= FIRST term  (x/(2q))log x (log(2UV/q+4)+4)
#   blocks part   (2d >  q)   <- should be <= SECOND term 0.89(UV+2.5q)(8+log q)log 2x
# Test both alpha = 1/(4q) (adversarial) and a few generic alphas.

def parts(x, q, UV, al):
    C = 4 * log(2) * log(2 * x)
    small = 0.0
    blocks = 0.0
    for d in range(1, UV + 1):
        if d % 2 == 0:
            continue
        Ad = 0.5 * (x / d) * log(x) + C
        sn = abs(math.sin(math.pi * 2 * al * d))
        Bd = C / sn if sn else float('inf')
        v = min(Ad, Bd)
        if 2 * d <= q:
            small += v
        else:
            blocks += v
    return small, blocks

def first_term(x, q, UV):
    return 0.5 * (x / q) * log(x) * (log(2 * UV / q + 4) + 4)

def second_term(x, q, UV):
    return 0.89 * (UV + 2.5 * q) * (8 + log(q)) * log(2 * x)

print(f"{'q':>6} {'UV':>8} {'xmul':>5} {'small':>12} {'T1':>12} {'s/T1':>7} "
      f"{'blocks':>12} {'T2':>12} {'b/T2':>7}  alpha")
worst_s = worst_b = 0.0
for q in [4, 10, 64, 100, 1000]:
    for UV in [1600, 10**4, 10**5]:
        if q > UV:
            continue
        for xmul in [4, 40, 400]:
            x = xmul * UV
            for al in [1 / (4 * q), 1 / (2 * q), 0.3121, 1 / 3]:
                s, b = parts(x, q, UV, al)
                T1 = first_term(x, q, UV)
                T2 = second_term(x, q, UV)
                rs, rb = s / T1, b / T2
                worst_s = max(worst_s, rs)
                worst_b = max(worst_b, rb)
                flag = "  <-- OVER" if (rs > 1 or rb > 1) else ""
                print(f"{q:6d} {UV:8d} {xmul:5d} {s:12.4e} {T1:12.4e} {rs:7.3f} "
                      f"{b:12.4e} {T2:12.4e} {rb:7.3f}  {al:.6f}{flag}")
print(f"\nWORST small/T1 = {worst_s:.4f}   WORST blocks/T2 = {worst_b:.4f}")
