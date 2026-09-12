import examples.«five-primes».CutoffPartition
import examples.«five-primes».FloorIntervalSum
import examples.«five-primes».TrapezoidAbel

open MeasureTheory
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

theorem sampled_eta1_sq_partition (x : ℝ) (hx : 0 < x) (n : ℕ) :
    eta1 ((n : ℝ) / x) ^ 2 =
      (if n ∈ Finset.Ioc ⌊x / 10⌋₊ ⌊x / 5⌋₊ then
        ((10 / x) * (n : ℝ) + (-1)) ^ 2 else 0) +
      (if n ∈ Finset.Ioc ⌊x / 5⌋₊ ⌊4 * x / 5⌋₊ then 1 else 0) +
      (if n ∈ Finset.Ioc ⌊4 * x / 5⌋₊ ⌊9 * x / 10⌋₊ then
        ((-10 / x) * (n : ℝ) + 9) ^ 2 else 0) := by
  have h1 : n ∈ Finset.Ioc ⌊x / 10⌋₊ ⌊x / 5⌋₊ ↔
      1 / 10 < (n : ℝ) / x ∧ (n : ℝ) / x ≤ 1 / 5 := by
    rw [mem_floor_Ioc_iff _ _ (by positivity) (by positivity),
      lt_div_iff₀ hx, div_le_iff₀ hx]
    constructor <;> rintro ⟨ha, hb⟩ <;> constructor <;> linarith
  have h2 : n ∈ Finset.Ioc ⌊x / 5⌋₊ ⌊4 * x / 5⌋₊ ↔
      1 / 5 < (n : ℝ) / x ∧ (n : ℝ) / x ≤ 4 / 5 := by
    rw [mem_floor_Ioc_iff _ _ (by positivity) (by positivity),
      lt_div_iff₀ hx, div_le_iff₀ hx]
    constructor <;> rintro ⟨ha, hb⟩ <;> constructor <;> linarith
  have h3 : n ∈ Finset.Ioc ⌊4 * x / 5⌋₊ ⌊9 * x / 10⌋₊ ↔
      4 / 5 < (n : ℝ) / x ∧ (n : ℝ) / x ≤ 9 / 10 := by
    rw [mem_floor_Ioc_iff _ _ (by positivity) (by positivity),
      lt_div_iff₀ hx, div_le_iff₀ hx]
    constructor <;> rintro ⟨ha, hb⟩ <;> constructor <;> linarith
  have h := eta1_sq_three_pieces ((n : ℝ) / x)
  simp only [← h1, ← h2, ← h3] at h
  have e1 : 10 * ((n : ℝ) / x) - 1 = (10 / x) * (n : ℝ) + (-1) := by ring
  have e3 : 9 - 10 * ((n : ℝ) / x) = (-10 / x) * (n : ℝ) + 9 := by ring
  simpa only [e1, e3] using h

theorem unsifted_quadratic_mass_abel (x : ℕ) (hx : 0 < x) :
    (∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) * eta1 ((n : ℝ) / x) ^ 2) =
    -(∫ t in Set.Ioc ((x : ℝ) / 10) ((x : ℝ) / 5),
        (2 * ((10 / (x : ℝ)) * t + (-1)) * (10 / (x : ℝ))) * Chebyshev.psi t) -
      ∫ t in Set.Ioc (4 * (x : ℝ) / 5) (9 * (x : ℝ) / 10),
        (2 * ((-10 / (x : ℝ)) * t + 9) * (-10 / (x : ℝ))) * Chebyshev.psi t := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hb (t : ℝ) (ht : t ≤ x) : ⌊t⌋₊ ≤ x := by
    simpa using Nat.floor_le_floor ht
  rw [← trapezoid_piecewise_abel (x : ℝ) hxpos]
  rw [← sum_range_indicator_Ioc x _ _ (hb _ (by linarith)),
    ← sum_range_indicator_Ioc x _ _ (hb _ (by linarith)),
    ← sum_range_indicator_Ioc x _ _ (hb _ (by linarith))]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [sampled_eta1_sq_partition (x : ℝ) hxpos n]
  split_ifs <;> ring

end TaoFivePrimes
