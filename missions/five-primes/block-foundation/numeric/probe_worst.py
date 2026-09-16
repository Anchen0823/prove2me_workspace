import math
log=math.log
# The theorem allows UV <= x/4  -- x may be ASTRONOMICALLY larger than UV.
# Envelope A-part ~ (1/4) x log x log(2UV/q). Target 1st term ~ (x/q) log x * 0.5*(log(2UV/q+4)+4)
# Ratio  ~ [0.25 x logx log(2UV/q)] / [0.5 (x/q) logx (log(2UV/q+4)+4)] = q/2 * log(2UV/q)/(log(2UV/q+4)+4)
# For fixed UV, ratio grows like q  => pick q as LARGE as possible: q ~ UV.
# And to make the log ratio favourable pick UV/q small... but q~UV gives 2UV/q=2.
print("### WORST CASE: q ~ UV, x >> UV (x = 4UV * 10^k) ###")
print(f"{'UV':>8} {'q':>8} {'x':>14} {'env':>18} {'target':>18} {'ratio':>9}")
for UV in [1600, 10**4, 10**5]:
    for k in [0, 3, 6, 9]:
        x = 4*UV*10**k
        q = UV
        C=4*log(2)*log(2*x); al=1/(4*q); e=0.0
        for d in range(1,UV+1):
            if d%2==0: continue
            Ad=0.5*(x/d)*log(x)+C
            sn=abs(math.sin(math.pi*2*al*d))
            Bd=C/sn if sn else float('inf')
            e+=min(Ad,Bd)
        r1=0.5*(x/q)*log(x)*(log(2*UV/q+4)+4)
        r2=0.89*(UV+2.5*q)*(8+log(q))*log(2*x)
        print(f"{UV:>8} {q:>8} {x:>14} {e:>18.1f} {r1+r2:>18.1f} {e/(r1+r2):>9.4f}")
