import Definitions.Def_ZudilinZetaArith

/-!
# Zudilin (2001): the auxiliary function `f₀`, the saddle-point equation, and `C₀`, `C₁`

Third definition layer for

  W. Zudilin, *One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational*,
  Uspekhi Mat. Nauk 56:4 (2001), 149–150.
-/

namespace ZudilinZeta

/-- The polynomial whose zeros are the saddle points of Zudilin's note:

`(τ - η₀)^r (τ - η₁) ⋯ (τ - η_q) - τ^r (τ - η₀ + η₁) ⋯ (τ - η₀ + η_q)`. -/
noncomputable def charPoly (P : Params) (τ : ℂ) : ℂ :=
  (τ - (P.eta 0 : ℂ)) ^ P.r * ∏ j ∈ Finset.Icc 1 P.q, (τ - (P.eta j : ℂ))
    - τ ^ P.r * ∏ j ∈ Finset.Icc 1 P.q, (τ - (P.eta 0 : ℂ) + (P.eta j : ℂ))

/-- The auxiliary function

`f₀(τ) = r η₀ log(η₀ - τ) + ∑_{j=1}^q (η_j log(τ - η_j) - (η₀ - η_j) log(τ - η₀ + η_j))`
`       - 2 ∑_{j=1}^r η_j log η_j + ∑_{j=r+1}^q (η₀ - 2η_j) log(η₀ - 2η_j)`,

with the principal branch of the complex logarithm. -/
noncomputable def f0 (P : Params) (τ : ℂ) : ℂ :=
  (P.r : ℂ) * (P.eta 0 : ℂ) * Complex.log ((P.eta 0 : ℂ) - τ)
    + (∑ j ∈ Finset.Icc 1 P.q,
        ((P.eta j : ℂ) * Complex.log (τ - (P.eta j : ℂ))
          - ((P.eta 0 : ℂ) - (P.eta j : ℂ)) * Complex.log (τ - (P.eta 0 : ℂ) + (P.eta j : ℂ))))
    - 2 * (∑ j ∈ Finset.Icc 1 P.r, (P.eta j : ℂ) * Complex.log (P.eta j : ℂ))
    + ∑ j ∈ Finset.Icc (P.r + 1) P.q,
        ((P.eta 0 : ℂ) - 2 * (P.eta j : ℂ)) * Complex.log ((P.eta 0 : ℂ) - 2 * (P.eta j : ℂ))

/-- The logarithmic derivative `ψ` of the gamma function (the digamma function). -/
noncomputable def digamma (x : ℝ) : ℝ := deriv (fun t : ℝ => Real.log (Real.Gamma t)) x

/-- `C₀ = - Re f₀(τ₀)`. -/
noncomputable def C0 (P : Params) (τ₀ : ℂ) : ℝ := -(f0 P τ₀).re

/-- `C₁ = r m₁ + m₂ + ⋯ + m_{q-r} - (∫₀¹ φ(x) dψ(x) - ∫₀^{1/m_{q-r}} φ(x) dx/x²)`,
the Stieltjes integral against the digamma function `ψ` being written as
`∫₀¹ φ(x) ψ'(x) dx`. -/
noncomputable def C1 (P : Params) : ℝ :=
  ((P.r : ℝ) * (m P 1 : ℝ) + ∑ j ∈ Finset.Icc 2 (P.q - P.r), (m P j : ℝ))
    - ((∫ x in (0 : ℝ)..1, (phi P x : ℝ) * deriv digamma x)
        - ∫ x in (0 : ℝ)..(1 / (m P (P.q - P.r) : ℝ)), (phi P x : ℝ) / x ^ 2)

end ZudilinZeta
