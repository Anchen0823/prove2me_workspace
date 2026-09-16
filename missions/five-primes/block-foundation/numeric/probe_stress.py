import math
log=math.log
# To stress the A-branch we need B_d >= A_d for MANY d, i.e. C/|sin| >= (1/2)(x/d)log x.
# That needs d large relative to q AND |sin(2 pi alpha d)| tiny.
# The regime where the whole sum is A-dominated: alpha = k/(2d0) for the LARGEST d0 = UV,
# gives |sin|~0 at d=UV, but at small d sin is generic -> B small -> min = B.
# So the true structure: for d << UV the B-branch wins; for d ~ UV the A-branch wins.
# The worst case for the FIRST TERM is alpha ~ 1/(4q): sin(pi d/(2q)) small for d~q.
def env_full(x,q,UV,alpha):
    C=4*log(2)*log(2*x); s=0.0
    for d in range(1,UV+1):
        if d%2==0: continue
        Ad=0.5*(x/d)*log(x)+C
        sn=abs(math.sin(math.pi*2*alpha*d))
        Bd=C/sn if sn else float('inf')
        s+=min(Ad,Bd)
    return s
print("=== stress: UV close to q (short range), various x ===")
for q,UV in [(100,200),(100,150),(1000,1500)]:
    for x in [10**4,10**6,10**8]:
        best=(0,None)
        for a in range(1,2*q):
            if math.gcd(a,q)!=1: continue
            v=env_full(x,q,UV,a/(4*q))
            if v>best[0]: best=(v,a)
        sharp=0.25*x*log(x)*(log(2*UV/q+4)+4)
        tgt=0.5*(x/q)*log(x)*(log(2*UV/q+4)+4)
        C=4*log(2)*log(2*x)
        # the pure-A sum if ALL d took A:
        pureA=sum(0.5*(x/d)*log(x)+C for d in range(1,UV+1) if d%2 and d>q/2)
        print(f" q={q:5d} UV={UV:5d} x={x:9d} max_env={best[0]:13.1f} pureA={pureA:13.1f} sharp={sharp:13.1f} tgt={tgt:12.1f} ok_sharp={best[0]<=sharp}")
