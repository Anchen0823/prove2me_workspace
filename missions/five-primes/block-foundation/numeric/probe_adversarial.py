import math

# The theorem is UNIFORM in alpha with |beta| <= 1/q^2 and 4alpha = a/q + beta.
# So alpha can be as close to a/(4q) as 1/(4q^2) allows.
# Worst case: a/q = 1/2 -> alpha ~ 1/8 ; or a/q chosen so a*d/q is an integer
# for many d.  Let's hunt for the worst alpha for the *global* TI bound.

def envelope_sum(alpha, q, x, UV):
    """Tao's (5.14) envelope summed over odd d in (q/2, UV], with A=B/C split."""
    C = 4*math.log(2)*math.log(2*x)
    L = 0.5*x
    tot = 0.0
    for d in range(1, UV+1):
        if d % 2 == 0: continue
        A_d = (L/d)*math.log(x) + C
        sn = abs(math.sin(math.pi*2*alpha*d))
        B_d = C/sn if sn != 0 else float('inf')
        tot += min(A_d, B_d)
    return tot

def cor35_block_bound(q, x, j, alpha):
    C = 4*math.log(2)*math.log(2*x)
    L = 2*j*q + q/2
    X = 0.5*(x/L)*math.log(x)
    return X + 2*C + C*(2/math.pi)*q*math.log(4*q)

print("=== single block, adversarial alpha vs Tao RHS (count=2 form) ===")
q, x, UV = 4, 10**6, 100
C = 4*math.log(2)*math.log(2*x)
print(f"  C = 4 log2 log 2x = {C:.3f}   q={q} x={x}")
for a in [1, 3, 5, 7]:
    alpha = a/(4*q)
    for j in [0,1,5,20]:
        L = 2*j*q + q/2
        R = 2*(j+1)*q + q/2
        s = 0.0
        for d in range(math.floor(L)+1, math.floor(R)+1):
            if d % 2 == 0: continue
            sn = abs(math.sin(2*math.pi*d*alpha))
            s += min(0.5*(x/(2*j*q+q/2))*math.log(x) + C, C/sn if sn!=0 else float('inf'))
        rhs2 = cor35_block_bound(q, x, j, alpha)
        rhs1 = 0.5*(x/L)*math.log(x) + 8*math.log(2)*math.log(2*x) + C*(2/math.pi)*q*math.log(4*q)
        print(f"  a={a} j={j:3d}  sum={s:16.2f}  Tao_rhs(count2)={rhs2:16.2f}  ok2={s<=rhs2}   Tao_as_written={rhs1:16.2f} ok1={s<=rhs1}")
