The reduction proves
$$0<d_{2n}I_n<2^{-n}\qquad(n>0)$$
from the independently proved integral bound and the existing Rosser--Schoenfeld node. The latter remains an open formalization dependency.

Mathlib identifies $\log d_m$ with the Chebyshev function $\psi(m)$. The imported estimate and the certified lower bound for $\log2$ give
$$\log d_{2n}<2(1.03883)n<3n\log2,$$
hence $d_{2n}<8^n$. Multiplication by the positive integral estimate $I_n<16^{-n}$ gives the result.

This reuses the existing prime-estimate branch instead of creating a duplicate Rosser--Schoenfeld theorem. It does not claim that this dependency has already been formally proved.
