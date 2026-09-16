import math
log=math.log
# SANITY: at alpha = 1/(4q) EXACTLY the phase sin(pi*d/(2q)) is never 0 for
# integer d, and |sin| >= sin(pi/(2q)).  So B_d = C/|sin| <= C/sin(pi/(2q)).
# Is B_d <= A_d for all odd d in the block?  Check the *C-only* comparison:
#   C/|sin| <= A_d = (1/2)(x/d)log x + C   <=>   C(1/sin - 1) <= (1/2)(x/d) log x.
# With sin ~ pi/(2q), 1/sin - 1 ~ 2q/pi, so LHS ~ C*2q/pi ~ 0.64*C*q,
# RHS ~ (1/2)(x/(2(j+1)q))log x = x log x/(4(j+1)q).
# For j << x log x/(4*0.64*C*q^2) the A-alt wins; that's why sA/Xj ~ 4..87.
print("Direct check: is B_d <= A_d for every odd d in each block (alpha=1/(4q))?")
for q in [4,10,100]:
    x=10**6; UV=1000; alpha=1/(4*q); C=4*log(2)*log(2*x)
    bad=0; tot=0
    for j in range(int(UV/(2*q))+1):
        L=2*j*q+q/2; R=2*(j+1)*q+q/2
        for d in range(math.floor(L)+1, min(math.floor(R),UV)+1):
            if d%2==0: continue
            sn=abs(math.sin(math.pi*2*alpha*d))
            Ad=0.5*(x/d)*log(x)+C; Bd=C/sn if sn else float('inf')
            tot+=1
            if Bd<Ad: bad+=1
    print(f"  q={q:4d}  #odd d in blocks={tot:5d}  #where B<A = {bad}")
print()
print("=> so at alpha=1/(4q) the B-alternative NEVER wins on the block range;")
print("   the whole block sum is exactly sum_d A_d, which is ~ #blocks * (X_j * c_j)")
print("   with c_j = (1/2)log(1+2q/L_j) <= (1/2)log5, i.e. O(1) per block, NOT one X_j.")
print("   Total = sum_j X_j * c_j  ~ (1/2)log5 * sum_j X_j  (for small j).")
print()
print("=> sum_j X_j <= (x/2q) log(2UV/q+4) log x ; with log5/2=0.8047 the A-total")
print("   is ~0.80 * x log x log(2UV/q+4)/(2q)  vs target 0.5*(x/q)log x(log(2UV/q+4)+4)")
print("   ratio ~ 1.61 -- TOO BIG.  Confirmed numerically above (1.209 at q=4 growing).")
