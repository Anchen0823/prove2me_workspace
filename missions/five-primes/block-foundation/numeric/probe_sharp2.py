import math
log=math.log
# CORRECT worst-case: we want alpha maximizing sum_d min(A_d, C/|sin(2 pi alpha d)|).
# A_d decreases in d, so the max is achieved when sin is small for small d,
# i.e. alpha ~ k/(2*small odd d).  The clean worst case: alpha = 1/(4q) makes
# sin(pi d/(2q)) SMALL when d/q is small -> that IS the bad case for small d!
# Also alpha = (q-1)/(4q)... let's just scan a dense grid of rational a/(4q).
def env_full(x,q,UV,alpha):
    C=4*log(2)*log(2*x); s=0.0
    for d in range(1,UV+1):
        if d%2==0: continue
        Ad=0.5*(x/d)*log(x)+C
        sn=abs(math.sin(math.pi*2*alpha*d))
        Bd=C/sn if sn else float('inf')
        s+=min(Ad,Bd)
    return s
print("=== scan alpha = a/(4q), a odd coprime to q, find the true max ===")
for q in [4,10,100]:
    x=10**6; UV=2000
    best=(0,None)
    for a in range(1,4*q):
        if math.gcd(a,q)!=1: continue
        v=env_full(x,q,UV,a/(4*q))
        if v>best[0]: best=(v,a)
    sharp=0.25*x*log(x)*(log(2*UV/q+4)+4)
    tgt=0.5*(x/q)*log(x)*(log(2*UV/q+4)+4)
    print(f" q={q:4d}: max env = {best[0]:16.1f} at a={best[1]}  |  sharp={sharp:16.1f} ok={best[0]<=sharp} | target={tgt:16.1f} target_ok={best[0]<=tgt}")
