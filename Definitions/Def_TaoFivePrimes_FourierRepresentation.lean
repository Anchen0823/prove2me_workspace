import Mathlib.Analysis.Fourier.AddCircle
import Definitions.Def_TaoFivePrimes_RepresentationCount

/-!
# Finite Fourier sums for Tao's weighted representation count

The product below is the finite-sum form of equation (8.11) in Tao's
five-primes paper, https://arxiv.org/abs/1201.6656, at `K = 1000`.
The circle has period one and carries its probability Haar measure.
-/

open scoped BigOperators

namespace TaoFourierIdentity

/-- A finite polynomial in the characters of the unit circle. -/
noncomputable def fourierPolynomial {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (k : ι → ℤ) (α : AddCircle (1 : ℝ)) : ℂ :=
  ∑ i ∈ s, a i * fourier (k i) α

end TaoFourierIdentity

namespace TaoFivePrimes

/-- The circle-method integrand for the count, with three positive shift sums. -/
noncomputable def representationIntegrand (x H : ℕ) (α : AddCircle (1 : ℝ)) : ℂ :=
  TaoFourierIdentity.fourierPolynomial (Finset.range (x + 1))
    (fun n ↦ (siftedVonMangoldt x n * eta1 ((n : ℝ) / x) : ℝ))
    (fun n ↦ (n : ℤ)) α ^ 2 *
  TaoFourierIdentity.fourierPolynomial (Finset.range (x / 1000 + 1))
    (fun n ↦ (siftedVonMangoldt (x / 1000) n * eta0 (1000 * (n : ℝ) / x) : ℝ))
    (fun n ↦ (n : ℤ)) α *
  TaoFourierIdentity.fourierPolynomial (Finset.Icc 1 (H / 3)) (fun _ ↦ 1)
    (fun n ↦ (n : ℤ)) α ^ 3 * fourier (-(x : ℤ)) α

end TaoFivePrimes
