Proof of `ZudilinZeta.zetaR_eq_riemannZeta`.

For every integer k ≥ 2, Mathlib's identity
zeta_eq_tsum_one_div_nat_add_one_cpow (Mathlib/NumberTheory/LSeries/RiemannZeta.lean)
gives

  riemannZeta (k : ℂ) = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ (k : ℂ),

the exponent on the right being the complex number (k : ℂ). Since
Complex.cpow_natCast states x ^ (n : ℂ) = x ^ n for n : ℕ, the right-hand side is

  ∑' n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ k

termwise. On the other hand, by definition

  zetaR k = ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ k,

and Complex.ofReal_tsum pushes the embedding ℝ ↪ ℂ inside the series, so

  (zetaR k : ℂ) = ∑' n : ℕ, (1 : ℂ) / ((n : ℂ) + 1) ^ k,

which is exactly the same series. The hypothesis hk : 2 ≤ k enters only through
1 < re (k : ℂ), the convergence half-plane required by the Mathlib identity. ∎

This closes the bridge between the elementary zeta series used by the Zudilin
linear forms and the `riemannZeta` appearing in the mission goal.
