import examples.«five-primes».AbelErrorBound
import examples.«five-primes».AbelKernelMass
import examples.«five-primes».CutoffSumPartition

open MeasureTheory
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

theorem weighted_psi_difference (a b δ : ℝ) (hab : a ≤ b) (g : ℝ → ℝ)
    (hg : Continuous g) (hg0 : ∀ t ∈ Set.Ioc a b, 0 ≤ g t)
    (hψ : ∀ t ∈ Set.Ioc a b, |Chebyshev.psi t - t| ≤ δ) :
    |(∫ t in Set.Ioc a b, g t * Chebyshev.psi t) -
      (∫ t in Set.Ioc a b, g t * t)| ≤ δ * ∫ t in Set.Ioc a b, g t := by
  have hp : IntegrableOn (fun t => g t * Chebyshev.psi t) (Set.Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
      (Chebyshev.psi_mono.intervalIntegrable.continuousOn_mul hg.continuousOn)
  have ht : IntegrableOn (fun t => g t * t) (Set.Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
      ((hg.mul continuous_id).intervalIntegrable a b)
  have h := weighted_psi_error a b δ hab g hg hg0 hψ
  simp only [mul_sub, integral_sub hp ht] at h
  exact h

theorem unsifted_mass_error_of_uniform (x : ℕ) (hx : 0 < x) (δ : ℝ)
    (hψ : ∀ t ∈ Set.Ioc ((x : ℝ) / 10) (9 * (x : ℝ) / 10),
      |Chebyshev.psi t - t| ≤ δ) :
    |(∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) * eta1 ((n : ℝ) / x) ^ 2) -
      (2 / 3 : ℝ) * x| ≤ 2 * δ := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  let u : ℝ → ℝ := fun t => 2 * ((10 / (x : ℝ)) * t + (-1)) * (10 / (x : ℝ))
  let d : ℝ → ℝ := fun t => -(2 * ((-10 / (x : ℝ)) * t + 9) * (-10 / (x : ℝ)))
  have hu0 : ∀ t ∈ Set.Ioc ((x : ℝ) / 10) ((x : ℝ) / 5), 0 ≤ u t := by
    intro t ht
    dsimp [u]
    have h : 1 < (10 / (x : ℝ)) * t := by
      rw [div_mul_eq_mul_div, lt_div_iff₀ hxpos]
      linarith [ht.1]
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)
  have hd0 : ∀ t ∈ Set.Ioc (4 * (x : ℝ) / 5) (9 * (x : ℝ) / 10), 0 ≤ d t := by
    intro t ht
    dsimp [d]
    have h : 0 ≤ (-10 / (x : ℝ)) * t + 9 := by
      have hh : (10 / (x : ℝ)) * t ≤ 9 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hxpos]
        linarith [ht.2]
      rw [neg_div, neg_mul]
      linarith
    apply neg_nonneg.mpr
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) h)
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) hxpos.le)
  have hu := weighted_psi_difference ((x : ℝ) / 10) ((x : ℝ) / 5) δ
    (by linarith) u (by dsimp [u]; fun_prop) hu0 (by
      intro t ht
      exact hψ t ⟨ht.1, by linarith [ht.2]⟩)
  have hd := weighted_psi_difference (4 * (x : ℝ) / 5) (9 * (x : ℝ) / 10) δ
    (by linarith) d (by dsimp [d]; fun_prop) hd0 (by
      intro t ht
      exact hψ t ⟨by linarith [ht.1], ht.2⟩)
  have hk := trapezoid_kernel_integrals (x : ℝ) hxpos
  change (∫ t in Set.Ioc ((x : ℝ) / 10) ((x : ℝ) / 5), u t) = 1 ∧
    (∫ t in Set.Ioc (4 * (x : ℝ) / 5) (9 * (x : ℝ) / 10), d t) = 1 at hk
  rw [hk.1, mul_one] at hu
  rw [hk.2, mul_one] at hd
  have hm := unsifted_quadratic_mass_abel x hx
  have hmain := trapezoid_main_term (x : ℝ) hxpos
  have hD (f : ℝ → ℝ) :
      (∫ t in Set.Ioc (4 * (x : ℝ) / 5) (9 * (x : ℝ) / 10), d t * f t) =
      -(∫ t in Set.Ioc (4 * (x : ℝ) / 5) (9 * (x : ℝ) / 10),
        (2 * ((-10 / (x : ℝ)) * t + 9) * (-10 / (x : ℝ))) * f t) := by
    simp only [d, neg_mul, integral_neg]
  rw [sub_eq_add_neg, ← hD Chebyshev.psi] at hm
  rw [sub_eq_add_neg, ← hD (fun t => t)] at hmain
  have hu' := abs_le.mp hu
  have hd' := abs_le.mp hd
  apply abs_le.mpr
  dsimp [u] at hu'
  constructor <;> linarith

end TaoFivePrimes
