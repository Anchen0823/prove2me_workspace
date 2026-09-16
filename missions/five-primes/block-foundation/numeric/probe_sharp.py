import math
log=math.log
# SHARPENED CLAIM:  replace the first term
#     0.5*(x/q)*log x*(log(2UV/q+4)+4)
# by  0.25*x*log x*(log(2UV/q+4)+4)     [ i.e. 0.5*(x/q) -> 0.25*x, dropping 1/q ]
# Is the FULL envelope sum (worst case, min resolved per d)  bounded by it?
def env_full(x,q,UV,alpha):
    C=4*log(2)*log(2*x); s=0.0
    for d in range(1,UV+1):
        if d%2==0: continue
        Ad=0.5*(x/d)*log(x)+C
        sn=abs(math.sin(math.pi*2*alpha*d))
        Bd=C/sn if sn else float('inf')
        s+=min(Ad,Bd)
    return s
print("=== sharpened first term 0.25*x*log x*(log(2UV/q+4)+4) as bound ===")
for q in [4,10,100]:
    for UV in [1000,10000]:
        for x in [10**6,10**8]:
            worst=max(env_full(x,q,UV,a/(4*q)) for a in range(1,4*q,2) if math.gcd(a,q)==1) if q<=10 else env_full(x,q,UV,1/(4*q))
            sharp=0.25*x*log(x)*(log(2*UV/q+4)+4)
            print(f" q={q:4d} UV={UV:6d} x={x:9d} worst_env={worst:16.1f} sharp={sharp:16.1f} ok={worst<=sharp} ratio={worst/sharp:.4f}")
