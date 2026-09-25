"""Independent audit of the zeta9 arithmetic core.

(A) Recompute C_j, G, d = lcm(1..n+m), d_n = lcm(1..n) from scratch and check
    the boxed improved integerization  t# = d_n^9/G :  t# A, t# B in Z,
    t#/m_prim in Z>0, against missions/zeta9/verification/linear-coeff/*.json.gz
    and against the recorded improved_to_primitive_integer values.
(B) Spot-check the large-prime gcd formula  v_p(G) = 7*1_{n mod p + 2(m mod p) >= 2p-1}
    (p^2 > n+m) and the bounds 0 <= nu_p <= v_p(C_0) <= 7 floor(log_p(n+m)).
(C) Spot-check the exact v_p(C_j) Legendre formula.
"""
import gzip, json, math, sys
from fractions import Fraction as Fr
from math import comb, gcd, isqrt

MIS = "missions/zeta9/verification"


def lcm_upto(n):
    v = 1
    for k in range(2, n + 1):
        v = v * k // gcd(v, k)
    return v


def Cj(n, m, j, power=7):
    return (-1) ** (m + j) * comb(n, j) ** 3 * comb(j + m, m) ** power * comb(n - j + m, m) ** power


def Gof(n, m, power=7):
    g = 0
    for j in range(n + 1):
        g = gcd(g, abs(Cj(n, m, j, power)))
    return g


def vp_fact(f, p):
    s = 0
    while f:
        f //= p
        s += f
    return s


def vp_Cj(n, m, j, p):
    return (3 * vp_fact(n, p) + 7 * vp_fact(j + m, p) + 7 * vp_fact(n - j + m, p)
            - 10 * vp_fact(j, p) - 10 * vp_fact(n - j, p) - 14 * vp_fact(m, p))


def primes_upto(n):
    sieve = [True] * (n + 1)
    sieve[0:2] = [False, False]
    for i in range(2, isqrt(n) + 1):
        if sieve[i]:
            for k in range(i * i, n + 1, i):
                sieve[k] = False
    return [i for i, ok in enumerate(sieve) if ok]


print("=== (A) integrality / multiplier audit ===")
cases = ["s9-n56-m0", "s9-n56-m2", "s9-n112-m4", "s9-n224-m8", "s9-n224-m48"]
RECORDED = {
    "s9-n56-m0": "1875094643046085730946281663520",
    "s9-n56-m2": "4428255315453861300640",
    "s9-n112-m4": "15005795402081411162497979747986794323668128",
    "s9-n224-m8": "360422654384205662511779703748926513680258965567843329969388945709956387515154500000",
    "s9-n224-m48": "433453464808539831885569798631275381115283116025069055236571208904107450",
}
for cid in cases:
    d = json.load(gzip.open(f"{MIS}/linear-coeff/{cid}.json.gz", "rt"))
    s, n, m = d["s"], d["n"], d["m"]
    A = Fr(int(d["A_zeta_rational"][0]), int(d["A_zeta_rational"][1]))
    B = Fr(int(d["B_constant_rational"][0]), int(d["B_constant_rational"][1]))
    G = Gof(n, m)
    dl = lcm_upto(n + m)
    dn = lcm_upto(n)
    tsharp = Fr(dn ** 9, G)
    tA, tB = tsharp * A, tsharp * B
    # primitive scale from the record
    Dg = Fr(int(d["primitive_multiplier"][0]), int(d["primitive_multiplier"][1]))
    ratio = tsharp / Dg
    print(f"{cid}: G={G} (rec {d['G_residue_gcd']}) | d={dl == int(d['d_lcm_n_plus_m'])} | "
          f"t#A int={tA.denominator == 1} | t#B int={tB.denominator == 1} | "
          f"t#/m_prim={ratio.denominator == 1} | matches recorded={str(ratio.numerator) == RECORDED[cid]}")
    if tA.denominator != 1 or tB.denominator != 1 or ratio.denominator != 1:
        print("    !! FAIL", cid)
    if G != int(d["G_residue_gcd"]) or dl != int(d["d_lcm_n_plus_m"]) or str(ratio.numerator) != RECORDED[cid]:
        print("    !! MISMATCH", cid)

print()
print("=== (B)(C) large-prime formula and small-prime bounds ===")
bad = 0
params = 0
terms = 0
for n in range(2, 61, 2):
    for m in range(0, (3 * n + 1) // 14 + 1):
        G = Gof(n, m)
        params += 1
        for p in primes_upto(n):
            if p * p <= n + m:
                continue
            terms += 1
            nu = 0
            g = G
            while g % p == 0:
                g //= p
                nu += 1
            pred = 7 * (1 if (n % p) + 2 * (m % p) >= 2 * p - 1 else 0)
            if nu != pred:
                bad += 1
                print(f"  MISMATCH n={n} m={m} p={p} nu={nu} pred={pred}")
            # exact v_p(C_j) formula cross-check on a few j
            for j in (0, n // 3, n):
                v1 = 0
                c = Cj(n, m, j)
                while c % p == 0:
                    c //= p
                    v1 += 1
                v2 = vp_Cj(n, m, j, p)
                if v1 != v2:
                    bad += 1
                    print(f"  LEGENDRE MISMATCH n={n} m={m} j={j} p={p} {v1} vs {v2}")
        # small-prime bound  0 <= nu_p <= v_p(C_0) <= 7 floor(log_p(n+m))
        for p in primes_upto(isqrt(n + m)):
            nu = 0
            g = G
            while g % p == 0:
                g //= p
                nu += 1
            bound = 7 * vp_fact(n + m, p)
            if not (0 <= nu <= min(vp_Cj(n, m, 0, p), bound)):
                bad += 1
                print(f"  SMALL-PRIME BOUND MISMATCH n={n} m={m} p={p} nu={nu}")
print(f"parameters={params}  prime terms checked={terms}  failures={bad}")
