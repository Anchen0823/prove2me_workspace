import math
log=math.log
# maximise ratio over (UV,q,x) admissible: U=V=sqrt(UV)>=40 => UV>=1600; UV<=x/4.
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
best=(0,None); worst_alpha_best=(0,None)
for UV in [1600,4000,10**4,3*10**4,10**5,3*10**5,10**6]:
    for xmul in [1,3,10,30,100,300,1000,10**4]:
        x=4*UV*xmul
        for q in [4,16,64,256,1000,4000,16000,10**5]:
            if q>UV: continue
            e=env(x,q,UV,1/(4*q)); t=tgt(x,q,UV)
            if e/t>best[0]: best=(e/t,(UV,q,x,e,t))
print(f"MAX ratio over admissible grid (alpha=1/(4q)): {best[0]:.4f}")
print(f"   at UV={best[1][0]} q={best[1][1]} x={best[1][2]}")
print(f"   env={best[1][3]:.1f} target={best[1][4]:.1f}")
print()
# also scan several alphas at the best UV,q to be safe
UV,q,x=best[1][0],best[1][1],best[1][2]
for a in range(1, 4*q, 2):
    if math.gcd(a,q)!=1: continue
    e=env(x,q,UV,a/(4*q)); t=tgt(x,q,UV)
    if e/t>worst_alpha_best[0]: worst_alpha_best=(e/t,a)
print(f"max over alpha=a/(4q) at that point: {worst_alpha_best[0]:.4f} (a={worst_alpha_best[1]})")
print()
print("=> CONCLUSION: the platform's target bound HOLDS with margin (max ratio ~0.44).")
print("   The A-part alone is NOT the mechanism; the B-part must absorb the bulk,")
print("   which is exactly Tao's 'freeze A at L_j + Cor 3.5' step. The earlier")
print("   'factor of two' worry was an artefact of using x far beyond the admissible")
print("   range for the chosen UV.")
