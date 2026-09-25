"""Independent sign check of the contour identity (C1) in
missions/zeta9/research/analytic.md, for the small case n=2, m=0, s=9.

R(t) = 8/(t(t+1)(t+2))^3,  L = sum_{k>=1} R^(6)(k)/6!  (exact rational value
computed below from the partial-fraction closed form),  and

    I = int_{c-i.inf}^{c+i.inf} R(z) K_7(z) dz,   c = m+1/2 = 1/2,
    K_7(z) = pi^7 (302 cos(pi z) + 57 cos(3 pi z) + cos(5 pi z)) / (360 sin^7(pi z)).

Question: is  L = +(1/(2 pi i)) I  or  L = -(1/(2 pi i)) I ?
"""
import sys, os
sys.path.insert(0, os.path.join("tmp", "zeta7", "exact_packages"))
from mpmath import mp, mpf, mpc, pi, sin, cos, quad, zeta, log

mp.dps = 30
c = mpf(1) / 2


def R(z):
    return mpf(8) / (z * (z + 1) * (z + 2)) ** 3


def K7(z):
    return pi ** 7 * (302 * cos(pi * z) + 57 * cos(3 * pi * z) + cos(5 * pi * z)) / (
        360 * sin(pi * z) ** 7
    )


def integrand(y):
    zp = mpc(c, y)
    zm = mpc(c, -y)
    return R(zp) * K7(zp) + R(zm) * K7(zm)


I = mpc(0, 1) * quad(integrand, [0, 1, 2, 4, 8, 16])

# exact L from the closed form computed by hand and re-checked below
C = [1, -8, 1]                       # C_j
D = [mpf(-9) / 2, 0, mpf(9) / 2]     # D_j = C_j u_j
E = [mpf(12), mpf(-24), mpf(12)]     # E_j = C_j (u_j^2 + v_j)/2
H = [[mpf(1) / k ** 7 for k in range(1, 3 + 1)]]  # placeholder, replaced below
Hp = {r: [sum(mpf(1) / i ** r for i in range(1, j + 1)) for j in range(3)] for r in (7, 8, 9)}
A = 28 * sum(C)
B = -sum(E[j] * Hp[7][j] + 7 * D[j] * Hp[8][j] + 28 * C[j] * Hp[9][j] for j in range(3))
L = A * zeta(9) + B

print("A =", A)
print("B =", B)
print("L (closed form) =", L)
print()
print("I                =", I)
print("I/(2 pi i)       =", I / (2 * pi * mpc(0, 1)))
print("-I/(2 pi i)      =", -I / (2 * pi * mpc(0, 1)))
print()
print("L/I              =", L / I)
print("ratio * 2 pi i   =", (L / I) * 2 * pi * mpc(0, 1))
