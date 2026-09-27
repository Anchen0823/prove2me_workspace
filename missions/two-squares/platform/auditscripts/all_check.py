import itertools, math, random

N = 300
errs = []

# 1. explicit_family_identity
for n in range(-N, N + 1):
    lhs = 1 + (n * n - n + 1) ** 2
    rhs = (2 * n - 1) ** 2 + (n * n - n - 1) ** 2
    if lhs != rhs:
        errs.append(("identity", n))

# 2. explicit_family_chain
for n in range(4, N + 1):
    if not (1 < 2 * n - 1 < n * n - n - 1 < n * n - n + 1):
        errs.append(("chain", n))

# 3. explicit_family_solution
for n in range(4, N + 1):
    v = [1, n * n - n + 1, 2 * n - 1, n * n - n - 1]
    ok = (1**2 + v[1] ** 2 == v[2] ** 2 + v[3] ** 2)
    ok = ok and all(x > 0 for x in v)
    ok = ok and len(set(v)) == 4
    if not ok:
        errs.append(("solution", n, v))
print("after family checks:", errs[:10], len(errs))

# 4. parity_alignment exhaustive counterexamples
pc = []
for a, b, c, d in itertools.product(range(-24, 25), repeat=4):
    if a * a + b * b != c * c + d * d:
        continue
    d1 = ((a - c) % 2 == 0) and ((b - d) % 2 == 0)
    d2 = ((a - d) % 2 == 0) and ((b - c) % 2 == 0)
    if not (d1 or d2):
        pc.append((a, b, c, d))
print("parity_alignment counterexamples:", len(pc), pc[:10])

# 5. sum_sq_eq_iff_product exhaustive
sc = []
for a, b, c, d in itertools.product(range(-15, 16), repeat=4):
    lhs = a * a + b * b == c * c + d * d
    rhs = (a + c) * (a - c) == (d + b) * (d - b)
    if lhs != rhs:
        sc.append((a, b, c, d))
print("sum_sq_eq_iff_product counterexamples:", len(sc), sc[:10])

# 6. complete_parametrization: constructive witness search
def ffp(X, Y, U, V):
    if X == 0 and U == 0:
        return (0, 1, V, Y)
    g = math.gcd(abs(X), abs(U))
    p, r, s = g, X // g, U // g
    if s != 0 and Y % s == 0:
        q = Y // s
        if p * r == X and q * s == Y and p * s == U and q * r == V:
            return (p, q, r, s)
    if r != 0 and V % r == 0:
        q = V // r
        if p * r == X and q * s == Y and p * s == U and q * r == V:
            return (p, q, r, s)
    return None

cc = []
tot = 0
for a, b, c, d in itertools.product(range(-30, 31), repeat=4):
    if a * a + b * b != c * c + d * d:
        continue
    tot += 1
    found = None
    for (X, Y, U, V, ac, bd, ad, bc) in [
        ((a + c) // 2, (a - c) // 2, (b + d) // 2, (d - b) // 2, a - c, b - d, a - d, b - c)
    ]:
        pass
    # branch 1 needs Even(a-c) and Even(b-d)
    if (a - c) % 2 == 0 and (b - d) % 2 == 0:
        X, Y, U, V = (a + c) // 2, (a - c) // 2, (b + d) // 2, (d - b) // 2
        w = ffp(X, Y, U, V)
        if w:
            p, q, r, s = w
            ok = (a == p * r + q * s and b == p * s - q * r and c == p * r - q * s and d == p * s + q * r)
            if ok:
                found = 1
    if found is None and (a - d) % 2 == 0 and (b - c) % 2 == 0:
        X, Y, U, V = (a + d) // 2, (a - d) // 2, (b + c) // 2, (c - b) // 2
        w = ffp(X, Y, U, V)
        if w:
            p, q, r, s = w
            ok = (a == p * r + q * s and b == p * s - q * r and d == p * r - q * s and c == p * s + q * r)
            if ok:
                found = 2
    if found is None:
        # brute force witness search as last resort
        res = None
        K = 60
        for p in range(-K, K + 1):
            for s in range(-K, K + 1):
                # solve a+c=2pr, a-c=2qs, b+d=2ps, d-b=2qr
                pass
        cc.append((a, b, c, d))
print("complete_param tuples:", tot, "unresolved:", len(cc), cc[:10])

# 7. sum_sq_eq_halves witness check for small instances
sh = []
for a, b, c, d in itertools.product(range(-12, 13), repeat=4):
    if a * a + b * b != c * c + d * d:
        continue
    if (a - c) % 2 == 0 and (b - d) % 2 == 0:
        X, Y, U, V = (a + c) // 2, (a - c) // 2, (b + d) // 2, (d - b) // 2
        if not (X + Y == a and X - Y == c and U - V == b and U + V == d and X * Y == U * V):
            sh.append((a, b, c, d))
print("sum_sq_eq_halves failures:", len(sh), sh[:10])

# 8. family_primitive
fp = []
for n in range(-200, 201):
    g = math.gcd(math.gcd(1, abs(n * n - n + 1)), math.gcd(abs(2 * n - 1), abs(n * n - n - 1)))
    if g != 1:
        fp.append(n)
print("family_primitive failures:", len(fp), fp[:5])

# 9. injectivity of family map
def fam(n):
    return (1, n * n - n + 1, 2 * n - 1, n * n - n - 1)

vals = {}
coll = []
for n in range(-2000, 2001):
    v = fam(n)
    if v in vals:
        coll.append((vals[v], n))
    vals[v] = n
print("injectivity collisions:", len(coll), coll[:5])

# 10. scaling trivial: any (m,n,k) satisfying hypothesis with n != m?
st = []
for k in range(-30, 31):
    for m in range(-30, 31):
        # first coordinate: 1 = k*1 -> k must be 1
        if k != 1:
            continue
        for n in range(-60, 61):
            if n == m:
                continue
            if (n * n - n + 1 == k * (m * m - m + 1) and 2 * n - 1 == k * (2 * m - 1)
                    and n * n - n - 1 == k * (m * m - m - 1)):
                st.append((m, n, k))
print("family_scaling_trivial violating instances:", len(st), st[:5])

# 11. two_squares_mul verified modulo various moduli (covers CommRing pathologies incl. char issues)
tm = []
for mod in [2, 3, 4, 6, 8, 12, 16, 30]:
    for _ in range(3000):
        p, q, r, s = [random.randrange(mod) for _ in range(4)]
        lhs = ((p * p + q * q) * (r * r + s * s)) % mod
        f1 = ((p * r + q * s) ** 2 + (p * s - q * r) ** 2) % mod
        f2 = ((p * r - q * s) ** 2 + (p * s + q * r) ** 2) % mod
        if lhs != f1 or lhs != f2:
            tm.append((mod, p, q, r, s))
print("two_squares_mul failures:", len(tm), tm[:5])

print("family errors total:", len(errs))
