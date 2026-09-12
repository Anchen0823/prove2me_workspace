import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The smoothed exponential sum of Tao's five-primes paper

Source: Terence Tao, https://arxiv.org/abs/1201.6656, Section 1, the display
defining `S_{η,q₀}(x,α)` immediately before equation (1.7).

The sum is unrestricted over `n : ℕ`; the cutoffs used in the paper are compactly
supported away from `0`, so only finitely many terms are nonzero.
-/

open scoped ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

/-- `expCircle θ = e(θ) = exp(2πiθ)`, the additive character of the paper. -/
noncomputable def expCircle (θ : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * θ)

/-- Tao's smoothed exponential sum

`S_{η,q₀}(x, α) = ∑ₙ Λ(n) e(αn) 1_{(n,q₀)=1} η(n/x)`,

for a cutoff `η`, a modulus `q₀`, a scale `x` and a phase `α`. -/
noncomputable def smoothedExpSum (η : ℝ → ℝ) (q₀ : ℕ) (x α : ℝ) : ℂ :=
  ∑' n : ℕ,
    if Nat.Coprime n q₀ then
      (Λ n : ℂ) * expCircle (α * n) * (η ((n : ℝ) / x) : ℂ)
    else 0

end TaoFivePrimes
