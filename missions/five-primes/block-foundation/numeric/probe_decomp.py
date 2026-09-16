import math
log=math.log
# DECOMPOSITION:  min(Xj+C, C/|sin|) <= min(Xj, C/|sin|) + C   [since min(a,b) <= min(a-c,b)+c]
# So sum_d min(Xj+C, C/|sin|) <= sum_d min(Xj, C/|sin|) + (#odd d in block)*C
#                            = Cor3.5(Xj, C) + (q/2 + O(1))*C
# Cor 3.5 on the block: count = floor(blockwidth/(2q))+1 = floor(2q/(2q))+1 = 2
#   => 2*(2*Xj + (2/pi)*C*q*log4q) = 4 Xj + 2(2/pi)C q log4q
# Tao's RHS:  Xj + 2C + (2/pi) C q log4q.  Ratio on the Xj part: Tao's 1*Xj vs Cor3.5's 4*Xj.
# => using Cor3.5 verbatim OVERSHOOTS by ~4Xj per block. Tao must use count=1.
# Check the count=1 form: 1*(2Xj + (2/pi)Cq log4q) = 2Xj + ...  still 2, not 1.
# => Tao splits at Xj/2?  Or he applies Cor 3.5 to HALF the block (even/odd split)?
print("VERIFY the key inequality needed:")
print("  sum_{d in block, odd} min(Xj, C/|sin(2 pi alpha d)|) <= 2*Xj + (2/pi)*C*q*log(4q)  ?")
def c35(x,q,j,al,UV):
    L=2*j*q+q/2; R=2*(j+1)*q+q/2
    C=4*log(2)*log(2*x); Xj=0.5*(x/L)*log(x)
    s=0.0
    for d in range(math.floor(L)+1, min(math.floor(R),UV)+1):
        if d%2==0: continue
        sn=abs(math.sin(math.pi*2*al*d)); s+=min(Xj, C/sn if sn else float('inf'))
    return s, 2*Xj+(2/math.pi)*C*q*log(4*q), Xj, C
for q in [4,10,100]:
    x=10**6; UV=10**5; al=1/(4*q); bad=0; tot=0; maxr=0
    for j in range(0, int(UV/(2*q))+1):
        s,rhs,Xj,C=c35(x,q,j,al,UV); tot+=1
        if s>rhs: bad+=1
        if rhs: maxr=max(maxr,s/rhs)
    print(f"  q={q:4d}: blocks={tot:6d} violating={bad}  max(s/rhs)={maxr:.4f}")
