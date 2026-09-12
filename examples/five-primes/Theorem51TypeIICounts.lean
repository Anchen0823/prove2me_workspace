import examples.«five-primes».Theorem51BlockCounting
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace TaoFivePrimes

theorem odd_row_count (s : Finset ℤ) (W : ℝ) (hW : 40 ≤ W)
    (hs : ∀ w ∈ s, W / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ W ∧ w % 2 = 1) :
    (s.card : ℝ) ≤ 1.1 * W / 4 := by
  have hc := odd_integer_interval_card s (W / 2) W (by linarith) hs
  linarith

theorem odd_column_count (s : Finset ℤ) (x W : ℝ) (hW : 0 < W)
    (hxW : 40 ≤ x / W)
    (hs : ∀ d ∈ s, x / (2 * W) ≤ (d : ℝ) ∧ (d : ℝ) ≤ x / W ∧ d % 2 = 1) :
    (s.card : ℝ) ≤ 1.1 * x / (4 * W) := by
  have he : x / (2 * W) = (x / W) / 2 := by ring
  have hc := odd_integer_interval_card s (x / (2 * W)) (x / W) (by rw [he]; linarith) hs
  rw [he] at hc
  have he' : 1.1 * x / (4 * W) = 1.1 * (x / W) / 4 := by ring
  rw [he']
  linarith

/-- Combining both odd counts with the half-log coefficient gives the
exact 1.1/8 prefactor in the pointwise Type II estimate. -/
theorem typeII_counting_constant (C x W D N : ℝ) (hC : 0 ≤ C) (hx : 0 ≤ x)
    (hW : 40 ≤ W) (hD0 : 0 ≤ D) (hN0 : 0 ≤ N)
    (hD : D ≤ 1.1 * x / (4 * W)) (hN : N ≤ 1.1 * W / 4) :
    Real.sqrt (C * D * (N / 4 * Real.log W ^ 2)) ≤
      (1.1 / 8) * Real.sqrt (C * x) * Real.log W := by
  have hw : 0 < W := by linarith
  have hlog : 0 ≤ Real.log W := Real.log_nonneg (by linarith)
  have hprod : D * N ≤ (1.1 ^ 2 / 16) * x := by
    have hp := mul_le_mul hD hN hN0 (show 0 ≤ 1.1 * x / (4 * W) by positivity)
    have he : (1.1 * x / (4 * W)) * (1.1 * W / 4) = (1.1 ^ 2 / 16) * x := by
      field_simp
      <;> ring
    rwa [he] at hp
  have hb := mul_le_mul_of_nonneg_left hprod (show 0 ≤ C * Real.log W ^ 2 / 4 by positivity)
  apply (Real.sqrt_le_left (by positivity)).mpr
  have hs := Real.sq_sqrt (mul_nonneg hC hx)
  nlinarith

end TaoFivePrimes
