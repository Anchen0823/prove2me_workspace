import math, sys
log=math.log
def env(x,q,UV,al):
    C=4*log(2)*log(2*x); s=0.0
    for d in range(1,UV+1,2):
        Ad=0.5*(x/d)*log(x)+C
        sn=abs(math.sin(math.pi*2*al*d))
        Bd=C/sn if sn else float('inf')
        s+=min(Ad,Bd)
    return s
def tgt(x,q,UV):
    return 0.5*(x/q)*log(x)*(log(2*UV/q+4)+4)+0.89*(UV+2.5*q)*(8+log(q))*log(2*x)
best=(0,None)
for UV in [1600,10**4,10**5]:
    for xmul in [1,10,100,1000]:
        x=4*UV*xmul
        for q in [4,64,1000,16000]:
            if q>UV: continue
            e=env(x,q,UV,1/(4*q)); t=tgt(x,q,UV)
            r=e/t
            if r>best[0]: best=(r,(UV,q,x))
            print(f"UV={UV:8d} q={q:6d} x={x:12d} ratio={r:.4f}", flush=True)
print(f"\nMAX ratio = {best[0]:.4f} at UV={best[1][0]} q={best[1][1]} x={best[1][2]}")
