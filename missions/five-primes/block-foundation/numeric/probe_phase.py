import math
# DECISIVE TEST.
# Node envelope phase:  sin(pi * (2*alpha) * d)      after cos_round: sin(pi*(2d)alpha)
# Cor 3.5 (Child 1) applies to:  min(A, B/|sin(pi*alpha0*n + theta)|)
#   and internally reindexes n = 2m+1 to Lemma 3.4 with alpha1 = 2*alpha0.
# So Cor 3.5 with alpha0 = alpha gives phase sin(pi*alpha*n), n=d odd.
# But the node phase is sin(pi*2*alpha*d) = sin(pi*alpha*(2d)) with 2d = n.
# s o  Cor 3.5 at alpha0 = 2*alpha matches the node phase EXACTLY.
# Then its block count is floor((y-x)/(2q)) + 1 with width (y-x) in the d-variable.
# A block of width 2q in d  =>  floor(2q/(2q)) + 1 = 2.   <-- still 2.
#
# UNLESS the intended block is half-Tao's: width q in d.  Then floor(q/(2q))+1 = 1.
print("count for width W in d, using floor(W/(2q))+1:")
for W in [4,8,10,20,40]:
    print(f"   W={W:3d} (q=4): floor({W}/8)+1 = {math.floor(W/8)+1}")
print()
# Tao writes blockwidth 2q (his 2(j+1)q+q/2 - (2jq+q/2) = 2q) => count 2.
# Tao's own RHS has '2A + ...' with A = X (he froze BEFORE adding C):
#   X + 8(log2)(log2x) + 4(log2)(log2x)(2/pi)q log 4q
#   = 1*X + 2*(4 log2 log2x) + 1*(2/pi)*B*q*log4q   where B = 4 log2 log2x
#   = 1*X + 2*C + 1*(2/pi)*C*q*log4q               <-- count 1!!
# So Tao's block bound has block count 1 for the cos term and a +2C = 2C from
# '2A' with A = C.  The mismatch is: he took A = X (not X+C) for the '2A' slot.
# Check whether  X + 2C + (2/pi)C q log4q  bounds the true block sum:
def test(C, X, alpha, q, j, form):
    L = 2*j*q + q/2; R = 2*(j+1)*q + q/2
    s = 0.0
    for d in range(math.floor(L)+1, math.floor(R)+1):
        if d % 2 == 0: continue
        sn = abs(math.sin(2*math.pi*d*alpha))
        s += min(X + C, C/sn if sn != 0 else float('inf'))
    if form == 'count1_X+2C':   rhs = X + 2*C + (2/math.pi)*C*q*math.log(4*q)
    if form == 'count1_X+8C':   rhs = X + 8*C + (2/math.pi)*C*q*math.log(4*q)
    if form == 'count2':        rhs = 2*X + 4*C + 2*(2/math.pi)*C*q*math.log(4*q)
    return s, rhs

print("worst-case single block (alpha = a/(4q) exactly -> adversarial):")
for q in [4,10]:
    for a in [1,2,3]:
        alpha = a/(4*q)
        for j in [0,3]:
            x = 10**6; C = 4*math.log(2)*math.log(2*x)
            L = 2*j*q+q/2; X = 0.5*(x/L)*math.log(x)
            for form in ['count1_X+2C','count1_X+8C','count2']:
                s, rhs = test(C,X,alpha,q,j,form)
                print(f"  q={q:3d} a={a} j={j} {form:14s} sum={s:12.2f} rhs={rhs:14.2f} ok={s<=rhs}")
