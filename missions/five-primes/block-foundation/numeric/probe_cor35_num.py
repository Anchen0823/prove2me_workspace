import math

# Corollary 3.5: sum over odd d in (x,y] of min(A, B/|sin(pi*alpha*d+theta)|)
#              <= (floor((y-x)/(2q))+1) * (2A + (2/pi)*B*q*log(4q))
def cor35(alpha, theta, q, A, B, x, y):
    lo = math.floor(x); hi = math.floor(y)
    s = 0.0
    for d in range(lo+1, hi+1):
        if math.gcd(d,2) != 1: continue
        sn = abs(math.sin(math.pi*alpha*d + theta))
        s += min(A, B/sn if sn != 0 else float('inf'))
    cnt = math.floor((y-x)/(2*q)) + 1
    rhs = cnt * (2*A + (2/math.pi)*B*q*math.log(4*q))
    return s, rhs, cnt

# --- Tao's small-d range: sum_{d in Z, -q/2<=d<=q/2} 1_{(d,2)} min(2q, 1/|sin(2 pi d alpha)|)
#     <= (2/pi) q log 4q + 4q
# Here alpha = 1/(4q) (the main case a=1), so 2*pi*d*alpha = pi*d/(2q).
print("=== small-d (alpha = 1/(4q), theta=0) : claim (2/pi) q log 4q + 4q ===")
for q in [4, 5, 10, 100, 1000]:
    alpha = 1/(4*q)
    # note: real alpha approaches 1/(4q) but differs; use exactly 1/(4q) for illustration
    # sum over d in [-q/2, q/2] odd, using symmetry = 2*sum over 1<=d<=q/2 odd + 0
    tot = 0.0
    for d in range(1, q//2+1):
        if d % 2 == 0: continue
        sn = abs(math.sin(2*math.pi*d*alpha))
        tot += min(2*q, 1/sn if sn != 0 else float('inf'))
    tot_sym = 2*tot   # symmetry d <-> -d
    rhs = (2/math.pi)*q*math.log(4*q) + 4*q
    print(f"  q={q:5d}  sum={tot_sym:12.4f}  rhs={rhs:12.4f}  slack={rhs-tot_sym:10.4f}  ok={tot_sym<=rhs}")
