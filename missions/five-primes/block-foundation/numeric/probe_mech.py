import math
log=math.log
# Tao's per-block bound:  X_j + 2C + (2/pi) C q log(4q)   [C = 4 log2 log2x]
# where X_j = (1/2)(x/L_j) log x.  He gets ONE X_j per block.
# How?  He does NOT sum over d; he applies Cor 3.5 with A = X_j fixed and B = C:
#   sum_d min(X_j + C, C/|sin|) <= sum_d min(X_j, C/|sin|) + (q/2)*C
# and Cor 3.5 on the block (count 1 in his accounting) gives
#   sum_{d in block} min(X_j, C/|sin|) <= 1*(2*X_j + (2/pi)*C*q*log 4q)
# -- the '2*A_X' slot gives 2*X_j, NOT one.  Then + (q/2)*C.
# So his RHS is  X_j + 8 log2 log2x + 4log2 log2x (2/pi) q log4q.
# Let us just CHECK: is  sum_d min(X_j+C, C/|sin|) <= X_j + 2C + (2/pi) C q log4q ?
def check(x,q,j,al,UV):
    L=2*j*q+q/2; R=2*(j+1)*q+q/2
    C=4*log(2)*log(2*x); Xj=0.5*(x/L)*log(x)
    s=0.0
    for d in range(math.floor(L)+1, min(math.floor(R),UV)+1):
        if d%2==0: continue
        Ad=Xj+C
        sn=abs(math.sin(math.pi*2*al*d)); Bd=C/sn if sn else float('inf')
        s+=min(Ad,Bd)
    return s, Xj+2*C+(2/math.pi)*C*q*log(4*q), Xj, C
print("=== Tao per-block RHS validity (alpha=1/(4q)) ===")
for q in [4,10,100]:
    x=10**6; UV=10**5; al=1/(4*q)
    bad=0; tot=0
    for j in range(0, int(UV/(2*q))+1):
        s,rhs,Xj,C = check(x,q,j,al,UV)
        tot+=1
        if s>rhs: bad+=1
    print(f"  q={q:4d}: blocks={tot:6d}  #violating Tao's per-block RHS = {bad}")
