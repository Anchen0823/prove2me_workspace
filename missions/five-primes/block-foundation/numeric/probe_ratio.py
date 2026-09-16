import math
log=math.log
# ANALYTIC ratio: env A-part  <=  S_A := (1/2) x log x * sum_{odd d in (q/2,UV]} 1/d + (#odd)*C
# Target 1st term T1 := 0.5*(x/q) log x * (log(2UV/q+4)+4).
# Sum_{odd d in (q/2,UV]} 1/d  <=  (1/2) log(2UV/q) + 1/(q)   (integral test step 2, + endpoint)
# So S_A / (x log x) <= (1/4) log(2UV/q) + 1/(2q)  +  C*UV/(2 x log x)  [last term negligible if x big]
# And T1/(x log x) = (1/(2q)) (log(2UV/q+4)+4).
# ratio = [ (1/4) log R + 1/(2q) ] / [ (1/(2q)) (log(R+4)+4) ]   where R = 2UV/q
#       = (q/2) * log R / (log(R+4)+4)  + log R/(log(R+4)+4) ... approx (q/2)*[logR/(log(R+4)+4)]
# This grows like q!  So for LARGE q (i.e. q >> log R) the ratio EXCEEDS 1.
print("### analytic ratio  (q/2)*logR/(log(R+4)+4)  with R = 2UV/q ###")
print(f"{'q':>8} {'UV':>12} {'R':>10} {'ratio_approx':>14}")
for UV in [10**4,10**6,10**8]:
    for q in [4,100,10**4,10**6,10**8]:
        if q>UV: continue
        R=2*UV/q
        # exact target-side uses log R only via the sum bound; use the true formula
        num=0.25*log(R)+1/(2*q)
        den=0.5*(log(R+4)+4)/q
        print(f"{q:>8} {UV:>12} {R:>10.4g} {num/den:>14.4f}")
print()
print("=> OVERSHOOT CONFIRMED analytically for q >> 1 with R bounded.")
print("   e.g. q=1e6, UV=1e8: R=200, ratio ~ (1e6/2)*log200/(log204+4) = 5e5*5.3/9.3 ~ 2.8e5")
print()
print("   SANITY: this needs x >= 4UV AND the C-part negligible: C*#odd <= 0.89*UV*...")
print("   Also alpha must be 1/(4q) EXACTLY so B never wins -- check that condition:")
print("   B_d >= A_d  <=>  C/|sin| >= (1/2)(x/d)log x + C  <=> C(1/|sin| - 1) >= (1/2)(x/d)log x")
print("   with |sin| = sin(pi d/(2q)) ~ pi d/(2q) for d << q:  LHS ~ C*2q/(pi d), RHS ~ x logx/(2d)")
print("   => need C*2q/pi >= x logx/2  <=> x <= 4Cq/pi/logx.  So B wins only for x not too large!")
print("   If x is LARGE, B wins only for d >= d* where (1/2)(x/d)logx <= C*2q/(pi d)")
print("   ... the 1/d cancels!  => B >= A  <=>  (1/2) x log x <= (2q/pi) C  <=> x log x <= (4q/pi) C.")
print("   Since C = 4 log2 log 2x ~ 2.77 log 2x, condition: x log x <= (4q/pi)*2.77*log2x")
print("   => x <= (11.08 q log 2x)/(pi log x) ~ 3.53 q  (since log2x ~ logx).")
print("   *** SO: B wins for ALL d iff  x <=~ 3.5 q.  Otherwise A wins for d large enough. ***")
