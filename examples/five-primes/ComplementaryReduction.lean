import examples.«five-primes».CircleTailIntegral
import examples.«five-primes».PrimeUniformBound

open MeasureTheory
open scoped BigOperators ArithmeticFunction.vonMangoldt ComplexConjugate

namespace TaoFivePrimes

theorem complementary_correlation_of_psi (x : ℕ) (hx : (10 ^ 9 : ℝ) ≤ x)
    (hrhi : T0 / (3.6 * Real.pi * (x : ℝ)) ≤ 1 / 2)
    (ε : ℝ) (hε : |ε| ≤ 0.02)
    (hpsi : (∑ n ∈ Finset.range (x + 1), (Λ n : ℝ)) ≤ 6 * (x : ℝ)) :
    ‖∫ α in (majorArc x)ᶜ, S1 x α *
      conj (TaoFourierIdentity.fourierPolynomial (Finset.range (x + 1))
        (fun n ↦ (eta1 ((n : ℝ) / x) : ℂ)) (fun n ↦ (n : ℤ)) α)
        ∂AddCircle.haarAddCircle‖ ≤
      0.01 * ((2 / 3 : ℝ) * (1 + ε) * x) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hx10 : 10 ≤ x := by exact_mod_cast (show (10 : ℝ) ≤ x by linarith)
  let r : ℝ := T0 / (3.6 * Real.pi * (x : ℝ))
  have hr : 0 < r := by dsimp [r, T0]; positivity
  have hsize : 5000 ≤ T0 / (3.6 * Real.pi) := by
    apply (le_div_iff₀ (by positivity : 0 < 3.6 * Real.pi)).2
    unfold T0
    nlinarith [Real.pi_lt_four]
  have hxr : (x : ℝ) * r = T0 / (3.6 * Real.pi) := by
    dsimp [r]
    field_simp
  have hdiv : 5 / ((x : ℝ) * r) ≤ 1 / 1000 := by
    apply (div_le_iff₀ (mul_pos hxpos hr)).2
    rw [hxr]
    linarith
  have hE : (majorArc x)ᶜ = {α : AddCircle (1 : ℝ) | r < ‖α‖} := by
    ext α
    simp [majorArc, r]
  let f : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨S1 x, TaoFourierIdentity.continuous_fourierPolynomial _ _ _⟩
  let g : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨TaoFourierIdentity.fourierPolynomial (Finset.range (x + 1))
      (fun n ↦ (eta1 ((n : ℝ) / x) : ℂ)) (fun n ↦ (n : ℤ)),
      TaoFourierIdentity.continuous_fourierPolynomial _ _ _⟩
  have hL1 : (∫ α in (majorArc x)ᶜ, ‖g α‖ ∂AddCircle.haarAddCircle) ≤ 1 / 1000 := by
    have h := cutoff_circle_tail_integral_bound x hx10 r hr hrhi
    rw [← hE] at h
    exact h.trans hdiv
  have hcorr := norm_correlation_le_uniform f g (majorArc x)ᶜ
    (6 * (x : ℝ)) (by
      intro α
      exact (S1_norm_le_prime_mass x α).trans hpsi)
  change ‖∫ α in (majorArc x)ᶜ, f α * conj (g α) ∂AddCircle.haarAddCircle‖ ≤ _
  calc
    _ ≤ (6 * (x : ℝ)) * ∫ α in (majorArc x)ᶜ, ‖g α‖
        ∂AddCircle.haarAddCircle := hcorr
    _ ≤ (6 * (x : ℝ)) * (1 / 1000) :=
      mul_le_mul_of_nonneg_left hL1 (by positivity)
    _ ≤ _ := by
      have he := (abs_le.mp hε).1
      have hmul := mul_nonneg (show 0 ≤ (x : ℝ) from hxpos.le)
        (show 0 ≤ ε + 0.02 by linarith)
      nlinarith

end TaoFivePrimes
