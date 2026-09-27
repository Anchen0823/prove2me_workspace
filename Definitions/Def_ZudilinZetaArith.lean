import Definitions.Def_ZudilinZetaSetup

/-!
# Zudilin (2001): the arithmetic factors `D_N`, `m_j`, `φ`, `Φₙ` and the form `Λₙ`

Second definition layer for

  W. Zudilin, *One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational*,
  Uspekhi Mat. Nauk 56:4 (2001), 149–150.
-/

namespace ZudilinZeta

/-- `D_N = lcm(1, 2, …, N)`. -/
def D (N : ℕ) : ℕ := (Finset.Icc 1 N).lcm id

/-- `m_j = max{η_r, η₀ - 2η_{r+1}, η₀ - η₁ - η_{r+j}}`, for `j = 1, …, q - r`. -/
def m (P : Params) (j : ℕ) : ℕ :=
  max (P.eta P.r) (max (P.eta 0 - 2 * P.eta (P.r + 1)) (P.eta 0 - P.eta 1 - P.eta (P.r + j)))

/-- The expression whose minimum over `0 ≤ y < 1` defines `φ(x)`:

`∑_{j=1}^r (⌊y⌋ + ⌊η₀x - y⌋ - ⌊y - η_j x⌋ - ⌊(η₀-η_j)x - y⌋ - 2⌊η_j x⌋)`
`+ ∑_{j=r+1}^q (⌊(η₀-2η_j)x⌋ - ⌊y - η_j x⌋ - ⌊(η₀-η_j)x - y⌋)`. -/
noncomputable def phiExpr (P : Params) (x y : ℝ) : ℤ :=
  (∑ j ∈ Finset.Icc 1 P.r,
      (⌊y⌋ + ⌊(P.eta 0 : ℝ) * x - y⌋ - ⌊y - (P.eta j : ℝ) * x⌋
        - ⌊((P.eta 0 : ℝ) - (P.eta j : ℝ)) * x - y⌋ - 2 * ⌊(P.eta j : ℝ) * x⌋))
  + ∑ j ∈ Finset.Icc (P.r + 1) P.q,
      (⌊((P.eta 0 : ℝ) - 2 * (P.eta j : ℝ)) * x⌋ - ⌊y - (P.eta j : ℝ) * x⌋
        - ⌊((P.eta 0 : ℝ) - (P.eta j : ℝ)) * x - y⌋)

/-- `φ(x) = min_{0 ≤ y < 1} φExpr(x, y)`, the integer-valued nonnegative function of
period 1 from Zudilin's note. -/
noncomputable def phi (P : Params) (x : ℝ) : ℤ :=
  sInf (phiExpr P x '' Set.Ico (0 : ℝ) 1)

/-- `Φₙ = ∏_{√(η₀ n) < p ≤ m_{q-r} n} p^{φ(n/p)}`, the product being over primes `p`
(the condition `√(η₀ n) < p` is written as `η₀ n < p²`). -/
noncomputable def Phi (P : Params) (n : ℕ) : ℕ :=
  ∏ p ∈ (Finset.Icc 1 (m P (P.q - P.r) * n)).filter
      (fun p => Nat.Prime p ∧ P.eta 0 * n < p * p),
    p ^ (phi P ((n : ℝ) / (p : ℝ))).toNat

/-- The normalized linear form appearing on the left-hand side of (3):
`Λₙ = D^r_{m₁ n} · D_{m₂ n} ⋯ D_{m_{q-r} n} · Φₙ⁻¹ · Fₙ`. -/
noncomputable def Lambda (P : Params) (n : ℕ) : ℝ :=
  ((D (m P 1 * n) : ℝ) ^ P.r * ∏ j ∈ Finset.Icc 2 (P.q - P.r), (D (m P j * n) : ℝ))
    / (Phi P n : ℝ) * F P n

end ZudilinZeta
