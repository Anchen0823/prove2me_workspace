import math
log = math.log
# The TRUE block sum, split into the A-dominated and B-dominated parts.
# Tao's goal per block:  one single X_j  (X_j = (1/2)(x/L_j) log x)  plus
#                        a cosecant piece.
# Question: with the min resolved PER-d, how much X_j comes out in total?
def true_block(x, q, alpha, j, UV):
    L = 2*j*q + q/2
    R = 2*(j+1)*q + q/2
    C = 4*log(2)*log(2*x)
    Xj = 0.5*(x/L)*log(x)
    sA = 0.0   # contribution where A_d <= B_d  (A-dominated)
    sB = 0.0   # contribution where B_d <  A_d
    nA = 0
    for d in range(math.floor(L)+1, min(math.floor(R), UV)+1):
        if d % 2 == 0: continue
        Ad = 0.5*(x/d)*log(x) + C
        sn = abs(math.sin(math.pi*2*alpha*d))
        Bd = C/sn if sn != 0 else float('inf')
        if Ad <= Bd:
            sA += Ad; nA += 1
        else:
            sB += Bd
    return sA, sB, Xj, nA

print("=== per-block A/B split, adversarial alpha = 1/(4q) (main case) ===")
for q in [4,10,100]:
    for UV in [1000]:
        for x in [10**6]:
            alpha = 1/(4*q)
            J = int(UV/(2*q))
            totA = totB = totX = 0.0
            for j in range(0, J+1):
                sA,sB,Xj,nA = true_block(x,q,alpha,j,UV)
                totA += sA; totB += sB; totX += Xj
            C = 4*log(2)*log(2*x)
            print(f"  q={q:4d} UV={UV} x={x}")
            print(f"     sum of per-block A-parts   = {totA:16.2f}   (counts ~ #blocks = {J+1})")
            print(f"     sum of per-block X_j       = {totX:16.2f}")
            print(f"     ratio totA/totX            = {totA/totX:.3f}")
            print(f"     sum of per-block B-parts   = {totB:16.2f}")
            print(f"     naive 1 x log x log(2UV/q)/4 = {0.5*x*log(x)*0.5*log(2*UV/q):16.2f}")
            print(f"     target                     = {0.5*(x/q)*log(x)*(log(2*UV/q+4)+4):16.2f}")
