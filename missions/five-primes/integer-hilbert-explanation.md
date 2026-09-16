For distinct integers $k_m$ and arbitrary complex coefficients $z_m$, we prove

$$
\left|\sum_m\sum_{n\ne m}\frac{\overline{z_m}z_n}{k_m-k_n}\right|
\le \frac72\sum_m |z_m|^2.
$$

The proof bounds the spectrum of the Hermitian matrix with entries
$i/(k_m-k_n)$, with zero diagonal, and then uses its orthonormal
eigenvector decomposition. No spacing or eigenvalue estimate is assumed.

For every row, injectivity of the integer indices gives

$$
\sum_{n\ne m}\frac{1}{(k_m-k_n)^2}
\le \sum_{r\in\mathbb Z}\frac{1}{r^2}
=\frac{\pi^2}{3}\le4,
$$

where the summand at zero is interpreted as zero. Apply the finite Hilbert
eigen-identity to a normalized eigenvector. After summing the identity over
its coordinates, the diagonal contribution is at most $4$. The cross term
is at most $8$, by the same row estimate and

$$
2\operatorname{Re}(u_m\overline{u_n})\le |u_m|^2+|u_n|^2.
$$

Thus each eigenvalue satisfies $\lambda^2\le12$, hence
$|\lambda|\le7/2$. Unitary diagonalization and preservation of the sum of
squared moduli extend this estimate to every coefficient vector. Finally,
multiplication by $i$ preserves the complex modulus and removes the factor
$i$ from the kernel.

The finite eigen-identity proof is adapted from the Apache-2.0
Zeta23.MV.EigenIdentity source by Anthropic (2026), with its copyright notice
preserved in the submitted file. The spectral expansion is adapted from
Zeta23.MV.star_dotProduct_mulVec_eq using Mathlib's spectral theorem directly.
All supporting proofs are included; no Open platform theorem is imported.

This provides an integer-grid input for the proposed Type II sine-kernel
estimate. The finite large-sieve bound, scale integration, and connection
to the original Tao theorem remain separate obligations.
