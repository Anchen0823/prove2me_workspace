import math
log=math.log
# The A-dominated regime: alpha = 1/(4q) makes sin(pi*d/(2q)) small when
# d/(2q) is small, i.e. d <~ q.  So the A-branch wins on the FIRST block
# (d in (q/2, 2q+q/2]) and the B-branch gradually takes over.
# => the envelope's A-part is ~ (q/2)*C + (1/2)x log x * sum_{d in first blocks} 1/d
#    which is ~ 0.5 * x log x * (1/2) log(4) = 0.25 x log x * log 2  (O(x log x)!)
#    -- INDEPENDENT of q.  Meanwhile the target's 1st term is 0.5*(x/q)log x*(...)
#    which is O(x log x / q).  So for LARGE q the envelope's A-part WINS.
# Need: d-range long enough that d ~ q ~ sqrt-ish. Let's construct:
#   UV large (need x >= 4UV), q chosen ~ sqrt(x) so q/2 << UV but x/q large.
print("### admissible counterexample: maximize  env / target ###")
print(" hyp: U=V>=40, UV<=x/4, q>=4, alpha=1/(4q) (a=1,beta=0)")
print()
print(f"{'UV':>8} {'q':>7} {'x':>12} {'env':>16} {'target':>16} {'ratio':>8}")
best=(0,None)
for UV in [10**4, 10**5, 10**6]:
    for q in [4, 10, 40, 100, 316, 1000, 3162, 10000]:
        if q>UV: continue
        x = 4*UV          # minimum admissible
        C=4*log(2)*log(2*x); al=1/(4*q); e=0.0
        for d in range(1,UV+1):
            if d%2==0: continue
            Ad=0.5*(x/d)*log(x)+C
            sn=abs(math.sin(math.pi*2*al*d))
            Bd=C/sn if sn else float('inf')
            e+=min(Ad,Bd)
        r1=0.5*(x/q)*log(x)*(log(2*UV/q+4)+4)
        r2=0.89*(UV+2.5*q)*(8+log(q))*log(2*x)
        rt=r1+r2
        rr=e/rt
        if rr>best[0]: best=(rr,(UV,q,x))
        print(f"{UV:>8} {q:>7} {x:>12} {e:>16.1f} {rt:>16.1f} {rr:>8.4f}")
print()
print(f"BEST: ratio={best[0]:.4f} at UV={best[1][0]} q={best[1][1]} x={best[1][2]}")
