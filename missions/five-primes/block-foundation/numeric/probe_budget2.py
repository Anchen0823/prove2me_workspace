import math
log=math.log
# Where should n*C go?  n <= q/2+1 odd d, each contributing C.
# Look at the ACTUAL block sum with A = Xj + C (the true envelope, frozen):
#   sum_d min(Xj + C, C/|sin|)
# and compare with Tao's RHS  Xj + 2C + (2/pi)Cq log4q.
def chk(x,q,j,al,UV):
    L=2*j*q+q/2; R=2*(j+1)*q+q/2
    C=4*log(2)*log(2*x); Xj=0.5*(x/L)*log(x)
    s=0.0; n=0
    for d in range(math.floor(L)+1, min(math.floor(R),UV)+1):
        if d%2:
            sn=abs(math.sin(math.pi*2*al*d))
            s+=min(Xj+C, C/sn if sn else float('inf')); n+=1
    return s, Xj+2*C+(2/math.pi)*C*q*log(4*q), n
print("TRUE envelope (frozen at Xj+C) vs Tao's per-block RHS:")
worst=(0,None)
for q in [4,10,100]:
    for x in [10**4,10**5,10**6,10**7]:
        UV=10**5; al=1/(4*q); bad=0; tot=0; wr=0
        for j in range(0,int(UV/(2*q))+1):
            l,r,n=chk(x,q,j,al,UV); tot+=1
            if l>r: bad+=1
            if r: wr=max(wr,l/r)
        print(f"  q={q:4d} x={x:9d}: blocks={tot:6d} viol={bad:5d} max={wr:.4f}")
        if wr>worst[0]: worst=(wr,(q,x))
print(f"\nWORST: {worst[0]:.4f} at {worst[1]}")
