import math
log=math.log
# CORRECT per-block A bound.  Sum over odd d in (L, R], L=2jq+q/2, R=L+2q.
# The odd d in (L,R] are: the q integers d = L+1, L+2, ..., R  filtered to odd.
# Antitone: t -> (1/2)(x/t) log x.  Sum over odd d <= integral over [L-1/2, R-1/2] step 2:
#   sum_{odd d in (L,R]} f(d) <= (1/2)*int_{L-1/2}^{R-1/2} f(t) dt
#                              = (1/2)*(1/2)x log x * log((R-1/2)/(L-1/2))
# R-1/2 = L+2q-1/2 ; ratio = (L+2q-1/2)/(L-1/2).
def perblock_correct(x,q,j):
    L=2*j*q+q/2; R=L+2*q
    ratio=(R-0.5)/(L-0.5)
    return 0.25*x*log(x)*log(ratio)
print("TRUE per-block A-part vs the CORRECT integral bound:")
for q in [4,10,100]:
    x=10**6
    for j in [0,1,5]:
        L=2*j*q+q/2; R=L+2*q
        sA=sum(0.5*(x/d)*log(x) for d in range(math.floor(L)+1, math.floor(R)+1) if d%2)
        b=perblock_correct(x,q,j)
        print(f"  q={q:4d} j={j:3d} L={L:8.1f}  sA={sA:14.2f}  correct_bound={b:14.2f}  ok={sA<=b}  ratio={b/sA if sA else 0:.3f}")
print()
print("And sum_j of that, vs the target:")
for q in [4,10,100]:
    x=10**6; UV=1000
    J=int(UV/(2*q)); tot=sum(perblock_correct(x,q,j) for j in range(J+1))
    tgt=0.5*(x/q)*log(x)*(log(2*UV/q+4)+4)
    print(f"  q={q:4d}: sum_j correct_perblock = {tot:15.2f}   target={tgt:15.2f}   ratio={tot/tgt:.3f}")
