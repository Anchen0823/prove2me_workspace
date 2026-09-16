import math
log=math.log
# The FINAL hblock:  b + (q/2+1)*C  <=  Xj + 2C + (2/pi) C q log4q
# where b = sum_{odd d in block} min(Xj, C/|sin|)  [Cor3.5 side]  -- I take b as the
# ACTUAL min-sum with A = Xj so the check is honest.
# Equivalently:  sum_d min(Xj, C/|sin|) + (q/2+1)C <= Xj + 2C + (2/pi)Cq log4q.
def check(x,q,j,al,UV):
    L=2*j*q+q/2; R=2*(j+1)*q+q/2
    C=4*log(2)*log(2*x); Xj=0.5*(x/L)*log(x)
    s=0.0; n=0
    for d in range(math.floor(L)+1, min(math.floor(R),UV)+1):
        if d%2:
            sn=abs(math.sin(math.pi*2*al*d))
            s+=min(Xj, C/sn if sn else float('inf')); n+=1
    lhs = s + n*C
    rhs = Xj + 2*C + (2/math.pi)*C*q*log(4*q)
    return lhs, rhs, n
print("FINAL hblock: lhs = Cor35_min_sum + n*C  <=  Xj + 2C + (2/pi)Cq log4q")
worst=(0,None)
for q in [4,10,100]:
    x=10**6; UV=10**5; al=1/(4*q); bad=0; tot=0; wr=0
    for j in range(0,int(UV/(2*q))+1):
        l,r,n=check(x,q,j,al,UV); tot+=1
        if l>r: bad+=1
        if r: wr=max(wr,l/r)
    print(f"  q={q:4d}: blocks={tot:6d} violations={bad}  max(lhs/rhs)={wr:.4f}")
print()
# Also sweep x to be safe
print("sweep x (q=10, UV=10000):")
for x in [10**3,10**4,10**5,10**6,10**7]:
    q=10; UV=10000; al=1/(4*q); bad=0; tot=0; wr=0
    for j in range(0,int(UV/(2*q))+1):
        l,r,n=check(x,q,j,al,UV); tot+=1
        if l>r: bad+=1
        if r: wr=max(wr,l/r)
    print(f"  x={x:9d}: violations={bad}  max(lhs/rhs)={wr:.4f}")
