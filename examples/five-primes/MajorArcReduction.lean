import examples.«five-primes».FourierMoments
import examples.«five-primes».LocalL2
import examples.«five-primes».CutoffEnergy

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace TaoFivePrimes

/-! A reduction with exactly two remaining analytic inputs: quadratic prime
mass and complementary correlation. The cutoff energy is proved locally. -/

theorem S1_raw_of_mass_and_tail (x : ℕ) (hx : (10 ^ 9 : ℝ) ≤ x)
    (ε : ℝ) (hε : |ε| ≤ 0.02)
    (hmass : (∑ n ∈ Finset.range (x + 1),
      siftedVonMangoldt x n * eta1 ((n : ℝ) / x) ^ 2) =
      (2 / 3 : ℝ) * (1 + ε) * x)
    (htail : ‖∫ α in (majorArc x)ᶜ, S1 x α *
      conj (TaoFourierIdentity.fourierPolynomial (Finset.range (x + 1))
        (fun n ↦ (eta1 ((n : ℝ) / x) : ℂ)) (fun n ↦ (n : ℤ)) α)
        ∂AddCircle.haarAddCircle‖ ≤
      0.01 * ((2 / 3 : ℝ) * (1 + ε) * x)) :
    0.999 * (0.99 * (1 + ε)) ^ 2 * x ≤ (3 / 2 : ℝ) *
      ∫ α in majorArc x, ‖S1 x α‖ ^ 2 ∂AddCircle.haarAddCircle := by
  let f : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨S1 x, TaoFourierIdentity.continuous_fourierPolynomial _ _ _⟩
  let g : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨TaoFourierIdentity.fourierPolynomial (Finset.range (x + 1))
      (fun n ↦ (eta1 ((n : ℝ) / x) : ℂ)) (fun n ↦ (n : ℤ)),
      TaoFourierIdentity.continuous_fourierPolynomial _ _ _⟩
  let M : ℝ := (2 / 3 : ℝ) * (1 + ε) * x
  let D : ℝ := (2 / 3 : ℝ) * x + 20
  have hxpos : (0 : ℝ) < x := by linarith
  have hM : 0 ≤ M := by
    have he := (abs_le.mp hε).1
    have hepos : 0 ≤ 1 + ε := by linarith
    dsimp [M]
    positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hE : MeasurableSet (majorArc x) := by
    exact isClosed_le continuous_norm continuous_const |>.measurableSet
  have hcorr : (∫ t, f t * conj (g t) ∂AddCircle.haarAddCircle) = (M : ℂ) := by
    change (∫ t, S1 x t * conj (TaoFourierIdentity.fourierPolynomial
      (Finset.range (x + 1)) (fun n ↦ (eta1 ((n : ℝ) / x) : ℂ))
      (fun n ↦ (n : ℤ)) t) ∂AddCircle.haarAddCircle) = (M : ℂ)
    rw [S1_cutoff_correlation, hmass]
  have henergy : (∫ t, ‖g t‖ ^ 2 ∂AddCircle.haarAddCircle) ≤ D := by
    change (∫ t, ‖TaoFourierIdentity.fourierPolynomial _ _ _ t‖ ^ 2
      ∂AddCircle.haarAddCircle) ≤ D
    rw [TaoFourierIdentity.integral_fourierPolynomial_norm_sq _ _ _ Nat.cast_injective]
    simpa [D, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      eta1_discrete_square_sum_le x (by exact_mod_cast hxpos)
  have hlocal := TaoLocalL2.local_energy_lower_bound f g (majorArc x) hE
    M (0.01 * M) D (by positivity) (by nlinarith) hD hcorr htail henergy
  have hprod := (div_le_iff₀ hD).mp hlocal
  have hprod' : (0.99 * ((2 / 3 : ℝ) * (1 + ε) * x)) ^ 2 ≤
      (∫ α in majorArc x, ‖S1 x α‖ ^ 2 ∂AddCircle.haarAddCircle) *
        ((2 / 3 : ℝ) * x + 20) := by
    change (M - 0.01 * M) ^ 2 ≤
      (∫ α in majorArc x, ‖S1 x α‖ ^ 2 ∂AddCircle.haarAddCircle) * D at hprod
    convert hprod using 1 <;> dsimp [M, D, f] <;> ring
  exact TaoLocalL2.normalized_major_arc_arithmetic_twenty (x : ℝ) ε _
    (by linarith) (integral_nonneg (fun _ => sq_nonneg _)) hprod'

end TaoFivePrimes
