"""Independent audit of the round5-round7 / roadmap layer of the zeta(9) mission.

Recomputes, from the construction itself (no reliance on the mission's scripts):

  R_n(t) = n!^7 * (t-n)_n * (t+n+1)_n / Q_n(t)^9,  Q_n(t) = prod_{j=0..n}(t+j),
  log R_n(k) = 7 lgamma(n+1) + 10 lgamma(k) - lgamma(k-n)
               + lgamma(k+2n+1) - 10 lgamma(k+n+1),
  f(x) = lim_n (1/n) log R_n(xn)
       = 10 x log x - (x-1) log(x-1) + (x+2) log(x+2) - 10 (x+1) log(x+1).

(A) locate the saddle x_*, the exponent f(x_*) and a = -f''(x_*); compare with the
    values claimed in the notes (-10.564155 < f_* < -10.564 ; 330.658 < a < 330.659 ;
    x_* ~ 1.00297646575).
(B) check the FQ designated sample points k_{n,j} = floor(n x_* + j sqrt(n/a) + 1/2),
    j = -2..2: are they distinct, and are they > n (required, since R_n(k)=0 for
    1 <= k <= n and the sum runs over k > n)?
(C) for a large n, compute the true moments M_e = sum_{k>n} R_n(k) (k(k+n)/n^2)^e,
    e = 0..4, solve the Vandermonde system for the five cubature weights, and check
    their signs and their limit against (1/12, 1/6, 1/2, 1/6, 1/12).
"""
import sys, os
sys.path.insert(0, os.path.join("tmp", "zeta7", "exact_packages"))
from mpmath import mp, mpf, log, loggamma, findroot, sqrt, matrix, lu_solve, floor

mp.dps = 50


def f(x):
    x = mpf(x)
    return (10 * x * log(x) - (x - 1) * log(x - 1)
            + (x + 2) * log(x + 2) - 10 * (x + 1) * log(x + 1))


def fp(x):
    x = mpf(x)
    return 10 * log(x) - log(x - 1) + log(x + 2) - 10 * log(x + 1)


def fpp(x):
    x = mpf(x)
    return 10 / x - 1 / (x - 1) + 1 / (x + 2) - 10 / (x + 1)


def h(eps):
    """equivalent condition, solved in eps = x-1 to avoid the x=1 singularity:
       (3+eps)(1+eps)^10 - eps(2+eps)^10 = 0"""
    eps = mpf(eps)
    return (3 + eps) * (1 + eps) ** 10 - eps * (2 + eps) ** 10


def hp(eps):
    eps = mpf(eps)
    return ((1 + eps) ** 10 + 10 * (3 + eps) * (1 + eps) ** 9
            - (2 + eps) ** 10 - 10 * eps * (2 + eps) ** 9)


eps = mpf("0.003")
for _ in range(200):
    eps = eps - h(eps) / hp(eps)
xs = 1 + eps

print("=== (A) saddle ===")
print("eps = x_*-1 =", mp.nstr(eps, 20))
print("x_*         =", mp.nstr(xs, 20), "  (round2 note: 1.00297646575)")
print("x_*        =", mp.nstr(xs, 20))
print("f(x_*)     =", mp.nstr(f(xs), 15), "   (notes: -10.564155 < f_* < -10.564)")
print("a = -f''    =", mp.nstr(-fpp(xs), 15), "   (notes: 330.658 < a < 330.659)")
print("sqrt(3/a)   =", mp.nstr(sqrt(3 / -fpp(xs)), 10), "  (notes: 0.095251<. <0.095252)")
print("y_* = x(x+1)=", mp.nstr(xs * (xs + 1), 12))
print("f(1+1/1000) =", mp.nstr(f(mpf(1001) / 1000), 12), " (round2 note: rate -10.5641538376)")

print()
print("=== (B) FQ designated sample points ===")
print("n        spacing   k_{n,-2..2}                distinct  all>n")
for n in [12, 24, 48, 96, 192, 384, 1000, 1400, 2000, 4000]:
    a = -fpp(xs)
    sp = sqrt(mpf(n) / a)
    ks = [int(floor(n * xs + j * sp + mpf(1) / 2)) for j in range(-2, 3)]
    print(f"{n:>6}  {mp.nstr(sp, 7):>9}  {str(ks):<24} {len(set(ks))==5!s:>8}  {all(k>n for k in ks)!s:>6}")

print()
print("=== (C) true-kernel five-point cubature ===")


def logR(n, k):
    return (7 * loggamma(n + 1) + 10 * loggamma(k) - loggamma(k - n)
            + loggamma(k + 2 * n + 1) - 10 * loggamma(k + n + 1))


def moments(n, e_max=4, kmax_factor=40):
    M = [mpf(0)] * (e_max + 1)
    nn = mpf(n)
    for k in range(n + 1, kmax_factor * n + 1):
        lr = logR(n, k)
        term = mp.e ** lr
        u = mpf(k) * (k + n) / nn ** 2
        for e in range(e_max + 1):
            M[e] += term * u ** e
    return M


for n in [1000, 2000, 6000]:
    M = moments(n)
    a = -fpp(xs)
    sp = sqrt(mpf(n) / a)
    Us = [mpf(k) * (k + n) / mpf(n) ** 2
          for k in [int(floor(n * xs + j * sp + mpf(1) / 2)) for j in range(-2, 3)]]
    V = matrix(5, 5)
    for i in range(5):
        for j in range(5):
            V[i, j] = Us[j] ** i
    rhs = matrix([M[e] / M[0] for e in range(5)])
    w = lu_solve(V, rhs)
    print(f"n={n}: points u_j = {[mp.nstr(u, 8) for u in Us]}")
    print(f"       weights  = {[mp.nstr(x, 8) for x in w]}   all positive = {all(x > 0 for x in w)}")
