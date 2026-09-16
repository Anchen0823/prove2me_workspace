import math
log=math.log
# EXACT envelope with alpha = 1/(4q), varying q/UV and x/UV.  No approximation.
def env(x,q,UV,al):
    C=4*log(2)*log(2*x); s=0.0
    for d in range(1,UV+1):
        if d%2==0: continue
        Ad=0.5*(x/d)*log(x)+C
        sn=abs(math.sin(math.pi*2*al*d))
        Bd=C/sn if sn else float('inf')
        s+=min(Ad,Bd)
    return s
def tgt(x,q,UV):
    return 0.5*(x/q)*log(x)*(log(2*UV/q+4)+4)+0.89*(UV+2.5*q)*(8+log(q))*log(2*x)
print("### exact, alpha=1/(4q), x = 4*UV*10^k, sweeping q ###")
print(f"{'UV':>8} {'q':>8} {'x':>16} {'env':>18} {'target':>18} {'ratio':>9}")
for UV in [10**4, 10**5, 10**6]:
    for k in [0,2,4,6]:
        x=4*UV*10**k
        for q in [4, 100, 10**3, 10**4, 10**5]:
            if q>UV: continue
            e=env(x,q,UV,1/(4*q)); t=tgt(x,q,UV)
            print(f"{UV:>8} {q:>8} {x:>16} {e:>18.1f} {t:>18.1f} {e/t:>9.4f}")
        print()
