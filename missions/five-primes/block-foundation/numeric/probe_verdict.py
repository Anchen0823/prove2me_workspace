import math
log=math.log
# DECISIVE. Take alpha = 1/(4q) EXACTLY (admissible: beta ~ 0), UV = q (so the
# d-range is just above q/2).  Then the envelope is *exactly* sum_{odd d in (q/2,q]} A_d
# and we can compute it in closed form-ish and compare to the target.
print(" q    | UV=q   x      Envelope_exact   Target_1st   2nd_term    Target_tot   Env/Target")
for q in [4,10,100,1000,10**4]:
    UV=q; x=10**6
    C=4*log(2)*log(2*x)
    env=sum(0.5*(x/d)*log(x)+C for d in range(1,UV+1) if d%2 and d>q/2)
    t1=0.5*(x/q)*log(x)*(log(2*UV/q+4)+4)
    t2=0.89*(UV+2.5*q)*(8+log(q))*log(2*x)
    print(f"{q:6d} | {UV:6d} {x:8d}  {env:14.1f}  {t1:13.1f}  {t2:11.1f}  {t1+t2:13.1f}   {env/(t1+t2):.4f}")
print()
print("Now with x much larger (x = q^4), UV = q:")
print(" q    | x=q^4        Envelope_exact   Target_tot     Env/Target")
for q in [4,10,100,1000]:
    UV=q; x=q**4
    C=4*log(2)*log(2*x)
    env=sum(0.5*(x/d)*log(x)+C for d in range(1,UV+1) if d%2 and d>q/2)
    t1=0.5*(x/q)*log(x)*(log(2*UV/q+4)+4)
    t2=0.89*(UV+2.5*q)*(8+log(q))*log(2*x)
    print(f"{q:6d} | {x:12d}  {env:14.1f}  {t1+t2:13.1f}   {env/(t1+t2):.4f}")
