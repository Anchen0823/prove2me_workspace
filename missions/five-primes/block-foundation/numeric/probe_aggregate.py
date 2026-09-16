import math

log = math.log

def target(x,q,UV):
    return 0.5*(x/q)*log(x)*(log(2*UV/q+4)+4) + 0.89*(UV + 2.5*q)*(8+log(q))*log(2*x)

def integral_bound(x,q,UV):
    return (x/(2*q))*log(2*UV/q+4)*log(x)

def blockcount_term(x,q,UV):
    return (UV/(2*q) + 1.25)*((2/math.pi)*q*log(4*q)+4*q)*4*log(2)*log(2*x)

print("=== ARCHITECTURE A: Tao-verbatim (count 2 per block, A=X frozen only) ===")
print(f"{'q':>4} {'UV':>7} {'x':>10} {'target':>16} {'A_sum':>16} {'ratio':>8}")
for q in [4,10,100]:
    for UV in [100,1000,10000]:
        for x in [10**4,10**6,10**8]:
            if UV > x/4: continue
            t = target(x,q,UV); a = integral_bound(x,q,UV)+blockcount_term(x,q,UV)
            print(f"{q:>4} {UV:>7} {x:>10} {t:>16.2f} {a:>16.2f} {a/t:>8.3f}")

print()
print("=== Is the OBVIOUS bound (integral test over ALL odd d, step 2) enough? ===")
# sum_{odd d>q/2, d<=UV} (1/2)(x/d) log x <= (1/2) x log x * (1/2) log(2UV/q) by integral test step 2
def naive_A(x,q,UV):
    # integral of 1/(2t) over [q/2, UV] = (1/2) log(2UV/q)
    return 0.5*x*log(x)*0.5*log(2*UV/q)
print(f"{'q':>4} {'UV':>7} {'x':>10} {'target':>16} {'naiveA':>16} {'ratio':>8}")
for q in [4,10,100]:
    for UV in [100,1000,10000]:
        for x in [10**4,10**6,10**8]:
            if UV > x/4: continue
            t = target(x,q,UV); a = naive_A(x,q,UV)
            print(f"{q:>4} {UV:>7} {x:>10} {t:>16.2f} {a:>16.2f} {a/t:>8.3f}")
