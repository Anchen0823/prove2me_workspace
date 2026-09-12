import Definitions.Def_TaoFivePrimes_FourierRepresentation

/-!
# The major/minor arc split in the proof of Tao's Theorem 8.2

Source: Terence Tao, https://arxiv.org/abs/1201.6656, Section 8, equations (8.11)–(8.12)
and the discussion following (8.16). Names for the three factors of the circle-method
integrand (8.11) at `K = 1000`, and the strongly major arc `‖α‖_{ℝ/ℤ} ≤ T₀/(3.6πx)` with
`T₀ = 3.29 × 10⁹` (Theorem 1.5).
-/

open scoped BigOperators

namespace TaoFivePrimes

/-- The height `T₀ = 3.29 × 10⁹` to which the Riemann hypothesis is numerically verified
(Theorem 1.5). -/
noncomputable def T0 : ℝ := 3.29 * 10 ^ 9

/-- `S_{η₁,√x♯}(x, α)`: the smoothed, sifted prime exponential sum with cutoff `η₁`
(the first two primes in (8.11)). -/
noncomputable def S1 (x : ℕ) (α : AddCircle (1 : ℝ)) : ℂ :=
  TaoFourierIdentity.fourierPolynomial (Finset.range (x + 1))
    (fun n ↦ (siftedVonMangoldt x n * eta1 ((n : ℝ) / x) : ℝ)) (fun n ↦ (n : ℤ)) α

/-- `S_{η₀,√(x/K)♯}(x/K, α)` at `K = 1000`: the smaller-scale sum with cutoff `η₀`
(Bourgain's trick, the third prime in (8.11)). -/
noncomputable def S0 (x : ℕ) (α : AddCircle (1 : ℝ)) : ℂ :=
  TaoFourierIdentity.fourierPolynomial (Finset.range (x / 1000 + 1))
    (fun n ↦ (siftedVonMangoldt (x / 1000) n * eta0 (1000 * (n : ℝ) / x) : ℝ))
    (fun n ↦ (n : ℤ)) α

/-- The Dirichlet-type kernel `D_{H/3}(α) = ∑_{1 ≤ n ≤ H/3} e(nα)`. -/
noncomputable def DK (H : ℕ) (α : AddCircle (1 : ℝ)) : ℂ :=
  TaoFourierIdentity.fourierPolynomial (Finset.Icc 1 (H / 3)) (fun _ ↦ 1) (fun n ↦ (n : ℤ)) α

/-- The strongly major arc `{α : ‖α‖_{ℝ/ℤ} ≤ T₀ / (3.6 π x)}` of Proposition 8.3. -/
def majorArc (x : ℕ) : Set (AddCircle (1 : ℝ)) :=
  {α | ‖α‖ ≤ T0 / (3.6 * Real.pi * x)}

/-- The integrand (8.11) is the product of the three named factors and the phase `e(-xα)`. -/
theorem representationIntegrand_eq (x H : ℕ) (α : AddCircle (1 : ℝ)) :
    representationIntegrand x H α = S1 x α ^ 2 * S0 x α * DK H α ^ 3 * fourier (-(x : ℤ)) α :=
  rfl

end TaoFivePrimes
