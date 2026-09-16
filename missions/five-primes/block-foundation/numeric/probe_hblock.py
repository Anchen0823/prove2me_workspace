import math
log=math.log
# Validate the FINAL hblock shape used in §10:
#   sum_{odd d in block} min(Xj/2, C/|sin(2 pi alpha d)|) <= (Xj/2) + (2/pi) C q log4q
# where Xj/2 is the frozen A.  [Cor 3.5 count 1 gives 2*(Xj/2) = Xj, plus the cos term.]
# Then block total <= Xj + (2/pi)Cq log4q + (q/2+1)C  <=  Xj + 2C + (2/pi)Cq log4q.
def check(x,q,j,al,UV):
    L=2*j*q+q/2; R=2*(j+1)*q+q/2
    C=4*log(2)*log(2*x); Xj=0.5*(x/L)*log(x)
    s=0.0; n=0
    for d in range(math.floor(L)+1, min(math.floor(R),UV)+1):
        if d%2: 
            sn=abs(math.sin(math.pi*2*al*d))
            s+=min(Xj/2, C/sn if sn else float('inf')); n+=1
    rhs=Xj/2+(2/math.pi)*C*q*log(4*q)
    total_rhs = Xj + 2*C + (2/math.pi)*C*q*log(4*q)
    return s, rhs, s+n*C, total_rhs, n
print("hblock shape check (alpha=1/(4q)); want s<=rhs and s+nC<=total_rhs")
for q in [4,10,100]:
    x=10**6; UV=10**5; al=1/(4*q)
    b1=b2=tot=0
    for j in range(0,int(UV/(2*q))+1):
        s,rhs,sn,total_rhs,n=check(x,q,j,al,UV); tot+=1
        if s>rhs: b1+=1
        if sn>total_rhs: b2+=1
    print(f"  q={q:4d}: blocks={tot:6d}  viol(hblock)={b1}  viol(block_total)={b2}")
