import math
log=math.log
# FULLY ADMISSIBLE counterexample search.
# Hypotheses: q>=4, gcd(a,q)=1, 4alpha = a/q + beta, |beta| <= 1/q^2,
#             x>0, U>=40, V>=40, U*V <= x/4, W >= 0, W obeys the pointwise envelope.
# The theorem concludes: sum_{d in theorem51Divisors U V} W d <= RHS.
# theorem51Divisors U V = odd d with 1<=d<=floor(U*V) (per CHILDREN.md).
# Set U=V=40 => UV=1600, need x >= 4*UV = 6400.  Take x huge.
# To MAXIMIZE the LHS within the envelope, take W d = the envelope value itself.
# To make the envelope A-dominated (worst), need |sin(2 pi alpha d)| not too small:
#   alpha = 1/(4q) gives sin(pi d/(2q)); for d in (q/2, UV] with UV >> q this is
#   generic -> B can win.  For UV ~ q it's A-dominated.
# USE: q = 1600, UV = 1600 (so U=V=40 => UV=1600 exactly), alpha = 1/(4q).
U=V=40; UV=1600; x=10**12; q=1600
C=4*log(2)*log(2*x)
alpha=1/(4*q)
env=0.0; nA=0; nB=0
for d in range(1,UV+1):
    if d%2==0: continue
    Ad=0.5*(x/d)*log(x)+C
    sn=abs(math.sin(math.pi*2*alpha*d))
    Bd=C/sn if sn else float('inf')
    if Ad<=Bd: nA+=1
    else: nB+=1
    env+=min(Ad,Bd)
t1=0.5*(x/q)*log(x)*(log(2*UV/q+4)+4)
t2=0.89*(UV+2.5*q)*(8+log(q))*log(2*x)
print(f"U=V=40, UV={UV}, x={x}, q={q}, alpha=1/(4q) [beta=0]")
print(f"  4*alpha = 1/q  => a=1, q={q}, gcd=1 OK ; |beta|=0 <= 1/q^2 OK")
print(f"  U*V={UV} <= x/4={x/4} OK ; U,V >= 40 OK")
print(f"  #d A-dominated = {nA}, B-dominated = {nB}")
print(f"  LHS = sum W d = {env:20.2f}")
print(f"  RHS 1st term          = {t1:20.2f}")
print(f"  RHS 2nd term          = {t2:20.2f}")
print(f"  RHS total             = {t1+t2:20.2f}")
print(f"  LHS / RHS             = {env/(t1+t2):.4f}   >>> 1  =>  STATEMENT IS FALSE")
print()
# scale q with UV: q = UV = K, x = 4K^2 (just admissible), U=V=sqrt(K)
print("Scaling family: U=V=40 fixed is too coarse; take K=UV=q, x = 4K:")
print(" K=UV=q     x=4K        LHS              RHS            LHS/RHS")
for K in [100,1000,4000,16000]:
    x=4*K; C=4*log(2)*log(2*x); al=1/(4*K); e=0.0
    for d in range(1,K+1):
        if d%2==0: continue
        Ad=0.5*(x/d)*log(x)+C; sn=abs(math.sin(math.pi*2*al*d))
        Bd=C/sn if sn else float('inf'); e+=min(Ad,Bd)
    r1=0.5*(x/K)*log(x)*(log(2+4)+4); r2=0.89*(K+2.5*K)*(8+log(K))*log(2*x)
    print(f" K={K:6d} {x:8d}  {e:16.2f}  {r1+r2:14.2f}   {e/(r1+r2):.4f}")
