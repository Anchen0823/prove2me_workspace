"""Corrected FQ audit: solve the five-point cubature in the WELL-SCALED
standardised variable s (nodes near -2..2), never in the ill-conditioned
variable u (nodes near 2.0 with 1e-3 spread, whose Vandermonde is numerically
singular at these precisions).

s_k = sqrt(a n)/(2 x_*+1) * (k(k+n)/n^2 - y_*),   k_{n,j} = floor(n x_* + j sqrt(n/a) + 1/2).

Reported: the exact five-point weights ω solving sum_j ω_j s_j^e = E[s^e] for e = 0..4,
their signs, and the standardised moments themselves vs the Gaussian (1,0,1,0,3).
Control: nodes exactly at s = -2..2 with Gaussian moments must give
(1/12, 1/6, 1/2, 1/6, 1/12).  A second control replaces the true moments by the
Gaussian ones at the same nodes.
"""
import sys, os
sys.path.insert(0, os.path.join("tmp", "zeta7", "exact_packages"))
from mpmath import mp, mpf, log, loggamma, sqrt, matrix, lu_solve, floor

mp.dps = 60


def h(e):
    return (3 + e) * (1 + e) ** 10 - e * (2 + e) ** 10


def hp(e):
    return ((1 + e) ** 10 + 10 * (3 + e) * (1 + e) ** 9 - (2 + e) ** 10
            - 10 * e * (2 + e) ** 9)


eps = mpf("0.003")
for _ in range(200):
    eps -= h(eps) / hp(eps)
xs = 1 + eps
a = -(10 / xs - 1 / (xs - 1) + 1 / (xs + 2) - 10 / (xs + 1))
ystar = xs * (xs + 1)
G = [mpf(1), mpf(0), mpf(1), mpf(0), mpf(3)]
GAUSS_W = [mpf(1) / 12, mpf(1) / 6, mpf(1) / 2, mpf(1) / 6, mpf(1) / 12]

print("control: nodes s = -2..2, Gaussian moments ->", [mp.nstr(x, 10) for x in
      lu_solve(matrix(5, 5, lambda i, j: mpf(j - 2) ** i), matrix(G))])

for n in [1000, 2000, 6000, 20000]:
    nn = mpf(n)
    c = sqrt(a * n) / (2 * xs + 1)
    Z = mpf(0)
    Ms = [mpf(0)] * 5
    for k in range(n + 1, 2 * n + 1):
        t = mp.e ** (7 * loggamma(n + 1) + 10 * loggamma(k) - loggamma(k - n)
                     + loggamma(k + 2 * n + 1) - 10 * loggamma(k + n + 1))
        s = c * (mpf(k) * (k + n) / nn ** 2 - ystar)
        Z += t
        for e in range(5):
            Ms[e] += t * s ** e
    std = [m / Z for m in Ms]
    sp = sqrt(nn / a)
    kint = [int(floor(nn * xs + j * sp + mpf(1) / 2)) for j in range(-2, 3)]
    sint = [c * (mpf(k) * (k + n) / nn ** 2 - ystar) for k in kint]
    sideal = [c * ((nn * xs + j * sp) * (nn * xs + j * sp + n) / nn ** 2 - ystar)
              for j in range(-2, 3)]
    print(f"\n--- n = {n} ---")
    print(f"  nodes k = {kint}   (all>n: {all(k > n for k in kint)}, distinct: {len(set(kint)) == 5})")
    print(f"  standardised node positions s_j = {[mp.nstr(x, 7) for x in sint]}")
    print(f"  true standardised moments E[s^e], e=0..4 : {[mp.nstr(x, 9) for x in std]}")
    print(f"  Gaussian reference                      : [1, 0, 1, 0, 3]")
    for tag, nodes in (("integer nodes", sint), ("ideal nodes", sideal)):
        V = matrix(5, 5, lambda i, j: nodes[j] ** i)
        w = lu_solve(V, matrix(std))
        print(f"  weights from true moments,   {tag}: {[mp.nstr(x, 8) for x in w]}"
              f"   all>0={all(x > 0 for x in w)}")
        w = lu_solve(V, matrix(G))
        print(f"  weights from Gaussian moments, {tag}: {[mp.nstr(x, 8) for x in w]}"
              f"   all>0={all(x > 0 for x in w)}")
    print(f"  claimed limit                           : {[mp.nstr(x, 10) for x in GAUSS_W]}")
