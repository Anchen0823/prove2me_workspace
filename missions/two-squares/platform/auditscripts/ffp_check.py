import itertools, math

def has_ffp(X, Y, U, V, K=80):
    """search p,q,r,s in [-K,K] with X=pr, Y=qs, U=ps, V=qr"""
    for p in range(-K, K + 1):
        if p != 0 and (X % p != 0 or U % p != 0):
            continue
        if p == 0 and (X != 0 or U != 0):
            continue
        for q in range(-K, K + 1):
            if q != 0 and (Y % q != 0 or V % q != 0):
                continue
            if q == 0 and (Y != 0 or V != 0):
                continue
            for r in range(-K, K + 1):
                if p * r != X or q * r != V:
                    continue
                for s in range(-K, K + 1):
                    if q * s != Y or p * s != U:
                        continue
                    return (p, q, r, s)
    return None

def ffp_construct(X, Y, U, V):
    """standard construction; returns witnesses or None"""
    if X == 0 and U == 0:
        return (0, 1, V, Y)
    g = math.gcd(abs(X), abs(U))
    p = g
    r = X // g
    s = U // g
    # need Y = q*s, V = q*r with gcd(r,s)=1
    if s != 0:
        if Y % s != 0:
            return None
        q = Y // s
    else:
        if V % r != 0:
            return None
        q = V // r
    if p * r == X and q * s == Y and p * s == U and q * r == V:
        return (p, q, r, s)
    # try q from other equation
    if r != 0:
        if V % r != 0:
            return None
        q2 = V // r
        if p * r == X and q2 * s == Y and p * s == U and q2 * r == V:
            return (p, q2, r, s)
    return None

bad = []
N = 14
count = 0
for X, Y, U, V in itertools.product(range(-N, N + 1), repeat=4):
    if X * Y != U * V:
        continue
    count += 1
    w = ffp_construct(X, Y, U, V)
    if w is None:
        bad.append((X, Y, U, V))
print("tuples checked:", count)
print("construction failures:", len(bad), bad[:20])

# independent brute-force check (no construction) for a smaller box
bad2 = []
cnt2 = 0
for X, Y, U, V in itertools.product(range(-6, 7), repeat=4):
    if X * Y != U * V:
        continue
    cnt2 += 1
    if has_ffp(X, Y, U, V, K=40) is None:
        bad2.append((X, Y, U, V))
print("brute tuples:", cnt2, "brute failures:", len(bad2), bad2[:20])
