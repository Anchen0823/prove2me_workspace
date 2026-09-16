import math
log = math.log

# RESOLUTION.
# For alpha = 1/(4q) exactly (the genuinely-adversarial main case), the phase is
#   sin(pi*2*alpha*d) = sin(pi*d/(2q)),  which is NEVER small:
#   min over odd d in (0,2q] of |sin(pi d/(2q))| = sin(pi/(2q)) ~ pi/(2q).
# So every min is resolved to A_d, and the block sum is exactly
#   sum_{d in block, odd} (1/2)(x/d)log x + C.
# The C-part:  q/2 terms * C each => (q/2) C per block  (NOT C!).
# The A-part:  sum_{d} (1/2)(x/d) log x  ~ X_j * (1/2) log(1+2q/L_j)
#              <= X_j * (1/2) log(1+2q/(q/2)) = X_j * (1/2) log 5  for j=0
#              and <= X_j * (1/2) log(1 + 2q/(2jq)) = X_j*(1/2)log(1+1/j)
# So per block:  A-part <= X_j * (1/2) log 5   (j=0)  /  X_j*(1/2)log(1+1/j) (j>=1)
# and C-part = (q/2)*C  = (2q) * (C/4).

print("=== EXACT per-block structure, alpha = 1/(4q) ===")
def block_exact(x,q,j,UV):
    L = 2*j*q+q/2; R = 2*(j+1)*q+q/2
    C = 4*log(2)*log(2*x)
    sA=sC=0.0; n=0
    for d in range(math.floor(L)+1, min(math.floor(R),UV)+1):
        if d%2: sA += 0.5*(x/d)*log(x); sC += C; n+=1
    Xj = 0.5*(x/L)*log(x)
    return sA, sC, n, Xj

for q in [4,10,100]:
    x=10**6; UV=1000
    J=int(UV/(2*q)); totA=totC=0.0; worst=[]
    for j in range(J+1):
        sA,sC,n,Xj = block_exact(x,q,j,UV)
        totA+=sA; totC+=sC
        if Xj>0: worst.append((sA/Xj, sC/(Xj if Xj>0 else 1), n, j))
    print(f" q={q:4d}: sum A-parts={totA:15.2f}  sum C-parts={totC:15.2f}")
    print(f"          max sA/Xj over blocks = {max(w[0] for w in worst):.4f}   (log5/2={log(5)/2:.4f})")
    print(f"          target                = {0.5*(x/q)*log(x)*(log(2*UV/q+4)+4):15.2f}")
    print(f"          A-parts as frac of target = {totA/(0.5*(x/q)*log(x)*(log(2*UV/q+4)+4)):.3f}")
