import math

# Tao's per-block claim:
#   sum_{2jq+q/2 < d <= 2(j+1)q+q/2, d odd} min(X + C, C/|sin(2 pi d alpha)|)
#     <= X + 8(log2)log2x + 4(log2)log2x * (2/pi) q log 4q
# where X = (1/2)(x/L_j) log x, C = 4(log2) log 2x,  L_j = 2jq+q/2.
# Note C/|sin| already has the C numerator; Tao writes the A-alt as X + C.
#
# Key question: is floor((blockwidth)/(2q)) + 1 == 1 for every j >= 0 ?
#   blockwidth = 2q  =>  (2q)/(2q) = 1  =>  floor(1)+1 = 2  !!!
# Tao says the block bound is X + 8(log2)log2x + 4(log2)log2x*(2/pi) q log 4q
#   = 1*(X) + 2*(2*C') + 1*(2/pi)*C'*q*log4q   with C' = 4log2 log2x
# Let's check numerically with the actual sum, using A = X + C and B = C.

def block_sum(X, C, alpha, theta, q, j, blockcount_mult=1):
    L = 2*j*q + q/2
    R = 2*(j+1)*q + q/2
    lo, hi = math.floor(L), math.floor(R)
    s = 0.0; cnt_terms = 0
    for d in range(lo+1, hi+1):
        if d % 2 == 0: continue
        sn = abs(math.sin(2*math.pi*d*alpha))
        val = C/sn if sn != 0 else float('inf')
        s += min(X + C, val)
        cnt_terms += 1
    return s, cnt_terms, L

print("=== per-block: is the count 1 or 2? ===")
q = 10; x = 10.0**6
C = 4*math.log(2)*math.log(2*x)
for j in [0,1,2,50,500]:
    X = 0.5*(x/(2*j*q+q/2))*math.log(x)
    # main case alpha ~ 1/(4q); use theta=0, alpha=1/(4q)
    alpha = 1/(4*q)
    s, cnt, L = block_sum(X, C, alpha, 0.0, q, j)
    # Tao's RHS
    rhs = X + 8*math.log(2)*math.log(2*x) + C*(2/math.pi)*q*math.log(4*q)
    # If count were 2: 2*(2*(X+C)) + 2*(2/pi)*C*q*log4q  -- clearly >> 
    print(f"  j={j:5d}  blockwidth={( 2*q )}  #odd_d={cnt:3d}  sum={s:14.4f}  Tao_rhs={rhs:14.4f}  ok={s<=rhs}")
print()
print("  => (2q)/(2q) = 1.0, floor(1.0) + 1 = 2.  Tao's stated block bound must NOT be")
print("     'Cor 3.5 applied verbatim with count=1'. Check the *shifted* endpoints:")
for q in [4,10,100]:
    for j in [0,1]:
        L = 2*j*q + q/2
        R = 2*(j+1)*q + q/2
        # Cor 3.5's reindexed form: x'=(L-1)/2, y'=(R-1)/2, q'=q, alpha'=2alpha
        xp, yp = (L-1)/2, (R-1)/2
        cnt = math.floor((yp-xp)/q) + 1
        print(f"  q={q:4d} j={j}  (x',y']=({xp:8.2f},{yp:8.2f}]  (y'-x')/q={(yp-xp)/q:.0f}  count={cnt}")
