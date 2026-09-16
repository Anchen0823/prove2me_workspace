import math
log=math.log
# DIAGNOSIS: the target's first term is 0.5*(x/q) log x (log(2UV/q+4)+4).
# The TRUE A-part (alpha=1/(4q), B never wins) is sum_{odd d in (q/2,UV]} (1/2)(x/d) log x
#   = 0.5*x*log(x) * sum_{odd d in (q/2,UV]} 1/d
#   ~ 0.5*x*log(x) * (1/2)*log(2UV/q)  = 0.25 x log x log(2UV/q).
# Compute exactly and compare with target.
def Aexact(x,q,UV):
    return sum(0.5*(x/d)*log(x) for d in range(1,UV+1) if d%2 and d>q/2)
print(f"{'q':>5} {'UV':>7} {'x':>10} {'A_exact':>16} {'target_1st':>16} {'A/tgt':>8} {'A/(x logx log(2UV/q)/4)':>10}")
for q in [4,10,100]:
    for UV in [1000,10000]:
        for x in [10**6,10**8]:
            A=Aexact(x,q,UV)
            t1=0.5*(x/q)*log(x)*(log(2*UV/q+4)+4)
            ref=0.25*x*log(x)*log(2*UV/q)
            print(f"{q:>5} {UV:>7} {x:>10} {A:>16.1f} {t1:>16.1f} {A/t1:>8.3f} {A/ref:>10.4f}")
print()
print("=> A_exact ~ 0.5*ref = (1/8) x log x log(2UV/q)??  Check: sum_{odd d in (q/2,UV]} 1/d")
for q in [4,100]:
    s=sum(1/d for d in range(1,10001) if d%2 and d>q/2)
    print(f"   q={q:4d}: sum 1/d = {s:.6f}   (1/2)log(2*10000/q) = {0.5*log(2*10000/q):.6f}")
print()
print("=> and target's 1st term / (x log x) = 0.5*(log(2UV/q+4)+4)/q.  Compare to sum 1/d:")
for q in [4,10,100]:
    s=sum(1/d for d in range(1,1001) if d%2 and d>q/2)
    print(f"   q={q:4d}: sum_{{odd d in (q/2,1000]}} 1/d = {s:.6f} ; 0.5*(log(2000/q+4)+4)/q = {0.5*(log(2000/q+4)+4)/q:.6f}")
