import math
log=math.log
# At alpha=1/(4q): sA/Xj grows like q.  Check the per-block A-part against the
# CORRECT per-block budget.  The block's own natural scale is
#    (1/2)(x/L_j) log x * (1/2) log(1 + 2q/L_j)   [integral test INSIDE the block,
#                                                 step 2, over the odd d]
# which is <= X_j * (1/2) log5.  But sum_j of THAT should be compared to the
# RHS x/(2q) log(2UV/q+4) log x obtained by the integral test on X_j itself.
print("Per-block A-part vs X_j * (1/2)log(1+2q/L_j):")
for q in [4,10,100]:
    x=10**6; UV=1000; tol=0.0
    for j in range(int(UV/(2*q))+1):
        L=2*j*q+q/2; R=2*(j+1)*q+q/2
        sA=0.0
        for d in range(math.floor(L)+1, min(math.floor(R),UV)+1):
            if d%2: sA+=0.5*(x/d)*log(x)
        Xj=0.5*(x/L)*log(x)
        bound=Xj*0.5*log(1+2*q/L)
        tol+=sA-bound
    print(f"  q={q:4d}:  sum(sA - Xj*(1/2)log(1+2q/Lj)) = {tol:.3f}  (<=0 expected)")
print()
print("=> and sum_j X_j*(1/2)log(1+2q/L_j) <= sum_j X_j * (1/2)log5")
print("   <= (x/2q)log(2UV/q+4) log x * 0.8047")
print("   ratio to target 0.5*(x/q)log x (log(2UV/q+4)+4) is ~1.61. STILL TOO BIG.")
print()
print("=== the actual issue: sum_d A_d over odd d>q/2 is NOT (x/2q)*anything;")
print("    sum_{odd d>q/2, d<=UV} (1/2)(x/d) log x = (1/2)x log x * sum_{odd d} 1/d")
print("    and sum_{odd d in (q/2,UV]} 1/d = (1/2)log(UV/(q/2)) + O(1) = (1/2)log(2UV/q)+O(1)")
print("    => (1/4) x log x log(2UV/q).  Compare to target's first term")
print("       0.5*(x/q) log x (log(2UV/q+4)+4):  LHS is BIGGER by ~ q/2.  So the")
print("       pure-A bound ALWAYS overshoots by a factor ~q/2 for large q.")
print()
print("    => Tao's 1/q CANNOT come from the A-part alone.  It must come from the")
print("       fact that the C-part (cosecant) DOMINATES for almost all d,")
print("       and the k=2q block aggregation is what produces (1/2q)*integral.")
